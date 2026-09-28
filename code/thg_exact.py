"""EXACT hook decompositions of the n-box from the T/H/G ansatz:
   Y_a(i,j) = 1/2 T(|i-j|,a) + 1/2 H(m'(i+j),a)   (i+j != n-1),   m'(x) = min(x+1, 2n-1-x)
   Y_a(i,j) = 1/2 T(|i-j|,a) + 1/2 G(|i-j|,a)      (i+j == n-1, main antidiagonal).
Hooks a <= A use the explicit image kernel T=H=img_a (exact recursion), G=0; the remaining hooks are solved by an
LP (HiGHS vertex) + exact rational re-solve on the support.  The full matrices are written in the stu3 certificate
format (a s i value) and checked by the coordinator's INDEPENDENT checker stu3/coord_check_hook.py."""
import sys, os, time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from sympy import QQ
from sympy.polys.matrices import DomainMatrix
from imgkernel import kernel

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'stu3'))
from coord_check_hook import check as indep_check


def mp(n, x): return min(x + 1, 2 * n - 1 - x)


def cellkeys(n, a, p, s):
    i, j = p, p + s
    return [('T', s, a), ('G', s, a) if i + j == n - 1 else ('H', mp(n, i + j), a)]


def solve_exact(n, A=None, seed=0, verbose=True):
    t0 = time.time()
    if A is None:
        A = -1
        while A + 1 < n - 1 and min(kernel(n, A + 1).values()) >= 0: A += 1
        A = min(A, n - 2)
    fixed = {}
    for a in range(A + 1):
        K = kernel(n, a)
        for s in range(a + 1): fixed[('T', s, a)] = K[s]
        for t in range(1, n):
            if t - 1 <= a: fixed[('H', t, a)] = K.get(t, F(0))
        for s in range((n - 1) % 2, n, 2):
            if s <= a: fixed[('G', s, a)] = F(0)
    idx = {}
    for a in range(A + 1, n):
        for s in range(a + 1): idx[('T', s, a)] = len(idx)
        for t in range(1, n):
            if t - 1 <= a: idx[('H', t, a)] = len(idx)
        for s in range((n - 1) % 2, n, 2):
            if s <= a: idx[('G', s, a)] = len(idx)
    rows = []  # (dict key->int coef, rhs Fraction)

    def add(d, rhs):
        dv, r = {}, F(rhs)
        for k, c in d.items():
            if k in idx: dv[k] = dv.get(k, 0) + c
            elif k in fixed: r -= c * fixed[k]
        rows.append((dv, r))
    for a in range(A + 1, n):
        for s in range(n):
            d = {}
            for p in range(n - s):
                for k in cellkeys(n, a, p, s): d[k] = d.get(k, 0) + 1
            add(d, 2 * (1 if s <= a else 0))
        for r in range(n):
            d = {}
            for j in range(n):
                p, s = min(r, j), abs(j - r)
                for k in cellkeys(n, a, p, s): d[k] = d.get(k, 0) + 1
            add(d, F(2 * (2 * a + 1), n))
    for s in range(n):
        for p in range(n - s):
            d = {}
            for a in range(s, n):
                for k in cellkeys(n, a, p, s): d[k] = d.get(k, 0) + 1
            add(d, 2)
    # drop rows that are identically zero in the variables (must have rhs 0)
    rr = []
    for dv, r in rows:
        dv = {k: c for k, c in dv.items() if c != 0}
        if not dv:
            assert r == 0, ('inconsistent fixed part', r)
        else:
            rr.append((dv, r))
    rows = rr
    keys = list(idx)
    R, C, V, b = [], [], [], []
    for k, (dv, r) in enumerate(rows):
        for key, c in dv.items(): R.append(k); C.append(idx[key]); V.append(float(c))
        b.append(float(r))
    Am = coo_matrix((V, (R, C)), shape=(len(rows), len(idx))).tocsr()
    rng = np.random.default_rng(seed + n)
    c = rng.uniform(0, 1, len(idx))
    res = linprog(c, A_eq=Am, b_eq=np.array(b), bounds=(0, None), method='highs-ds')
    if res.status != 0:
        if verbose: print(f'  n={n}: A={A} infeasible, retry with A={A-1}', flush=True)
        return solve_exact(n, A - 1, seed, verbose)
    supp = [j for j in range(len(idx)) if res.x[j] > 1e-10]
    col = {j: q for q, j in enumerate(supp)}
    # exact solve on the support
    Mrows = []
    for dv, r in rows:
        row = [QQ(0)] * (len(supp) + 1)
        ok = True
        for key, cf in dv.items():
            j = idx[key]
            if j in col: row[col[j]] = QQ(cf)
        row[-1] = QQ(r.numerator, r.denominator)
        Mrows.append(row)
    M = DomainMatrix(Mrows, (len(Mrows), len(supp) + 1), QQ).to_sparse()
    rref, piv = M.rref()
    piv = list(piv)
    assert len(supp) not in piv, 'inconsistent'
    assert len(piv) == len(supp), 'support not independent'
    rrm = rref.to_Matrix()
    sol = dict(fixed)
    for key in keys: sol[key] = F(0)
    for ri, cj in enumerate(piv):
        v = rrm[ri, len(supp)]
        sol[keys[supp[cj]]] = F(int(v.p), int(v.q))
    # expand to full hooks and write certificate
    x = {}
    for a in range(n):
        for s in range(a + 1):
            for p in range(n - s):
                k1, k2 = cellkeys(n, a, p, s)
                v = (sol.get(k1, F(0)) + sol.get(k2, F(0))) / 2
                if v != 0: x[(a, s, p)] = v
    assert all(v >= 0 for v in x.values()), 'negative entry'
    path = os.path.join(HERE, 'certs', f"thg{os.environ.get('THG_TAG', '')}_n{n}.txt")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write(f'# exact hook decomposition of the {n}-box (T/H/G ansatz, image kernel hooks 0..{A}): a s i value\n')
        for (a, s, p), v in sorted(x.items()):
            f.write(f'{a} {s} {p} {v}\n')
    t1 = time.time()
    ok = indep_check(n, path)
    den = max(v.denominator for v in x.values())
    if verbose:
        print(f'n={n}: A={A} (image-kernel hooks), LP vars={len(idx)}, support={len(supp)}, '
              f'independent exact check: {ok}, max den ~1e{len(str(den))-1}, solve {t1-t0:.1f}s, check {time.time()-t1:.1f}s',
              flush=True)
    return ok


if __name__ == '__main__':
    for n in [int(v) for v in sys.argv[1:]]:
        solve_exact(n)
