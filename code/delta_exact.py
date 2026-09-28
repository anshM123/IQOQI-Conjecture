"""EXACT certificate from the canonical-delta construction: hooks <= (n-1)/2 image kernel, (n-1)/2 < a <= n-1-k
canonical delta-modified image kernels (explicit Fractions), top k hooks by LP vertex + exact rational re-solve.
Writes certs/delta_n{n}.txt and checks it with the INDEPENDENT checker stu3/coord_check_hook.py."""
import sys, os, time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from sympy import QQ
from sympy.polys.matrices import DomainMatrix
import delta_model as dm
from delta_canon import canon
from imgkernel import kernel
sys.path.insert(0, os.path.join('..', 'stu3'))
from coord_check_hook import check as indep_check

def run(n, k):
    t0 = time.time()
    A = (n - 1) // 2
    idx, rows, nonneg = dm.build(n, A, k)
    deltas = {a: canon(n, a) for a in range(A + 1, n - k)}
    assert all(d is not None for d in deltas.values())
    # substitute deltas: remove ('d',a) variables
    var = [key for key in idx if key[0] != 'd']
    vid = {key: i for i, key in enumerate(var)}
    erows = []
    for d, rhs in rows:
        r = F(rhs); dd = {}
        for key, c in d.items():
            if key[0] == 'd': r -= F(c) * deltas[key[1]]
            else: dd[key] = dd.get(key, 0) + F(c)
        dd = {kk: c for kk, c in dd.items() if c != 0}
        if not dd: assert r == 0, ('inconsistent', r)
        else: erows.append((dd, r))
    for d, c0 in nonneg:   # check delta-part nonnegativity exactly
        val = F(c0) + sum(F(c) * deltas[key[1]] for key, c in d.items())
        assert val >= 0, 'negative delta hook entry'
    R, C, V, b = [], [], [], []
    for i, (dd, r) in enumerate(erows):
        for key, c in dd.items(): R.append(i); C.append(vid[key]); V.append(float(c))
        b.append(float(r))
    Aeq = coo_matrix((V, (R, C)), shape=(len(erows), len(var))).tocsr()
    rng = np.random.default_rng(n)
    res = linprog(rng.uniform(0, 1, len(var)), A_eq=Aeq, b_eq=np.array(b), bounds=(0, None), method='highs-ds')
    assert res.status == 0, res.message
    supp = [j for j in range(len(var)) if res.x[j] > 1e-10]
    col = {j: q for q, j in enumerate(supp)}
    Mrows = []
    for dd, r in erows:
        row = [QQ(0)] * (len(supp) + 1)
        for key, c in dd.items():
            j = vid[key]
            if j in col: row[col[j]] = QQ(c.numerator, c.denominator)
        row[-1] = QQ(r.numerator, r.denominator); Mrows.append(row)
    M = DomainMatrix(Mrows, (len(Mrows), len(supp) + 1), QQ).to_sparse()
    rref, piv = M.rref(); piv = list(piv)
    assert len(supp) not in piv and len(piv) == len(supp)
    rr = rref.to_Matrix()
    sol = {key: F(0) for key in var}
    for ri, cj in enumerate(piv):
        v = rr[ri, len(supp)]; sol[var[supp[cj]]] = F(int(v.p), int(v.q))
    # assemble kernels
    T = {}; H = {}; G = {}
    for a in range(A + 1):
        K = kernel(n, a)
        for l in range(a + 1):
            T[(l, a)] = K[l]
            if l >= 1: H[(l, a)] = K[l]
    for a, d in deltas.items():
        Ti, w = dm.dmod(n, a)
        for l in range(a + 1):
            T[(l, a)] = Ti[l] + d * w[l]
            if l >= 1: H[(l, a)] = T[(l, a)] - (d if l == a else 0)
        for u in range((n - 1) % 2, n, 2):
            if u <= 2 * a - n - 1: G[(u, a)] = d
    for key, v in sol.items():
        {'T': T, 'H': H, 'G': G}[key[0]][(key[1], key[2])] = v
    x = {}
    for a in range(n):
        for s in range(a + 1):
            for p in range(n - s):
                i, j = p, p + s
                v = (T.get((s, a), 0) + (G.get((s, a), 0) if i + j == n - 1 else H.get((dm.mp(n, i + j), a), 0))) / 2
                if v != 0: x[(a, s, p)] = F(v)
    assert all(v >= 0 for v in x.values())
    path = f'certs/delta_n{n}.txt'
    with open(path, 'w') as f:
        f.write(f'# exact hook decomposition of the {n}-box: image kernel a<={A}, canonical delta-modified image kernels '
                f'a<={n-1-k}, top {k} hooks by exact LP vertex: a s i value\n')
        for (a, s, p), v in sorted(x.items()): f.write(f'{a} {s} {p} {v}\n')
    ok = indep_check(n, path)
    print(f'n={n} k={k}: top-hook LP vars={len(var)}, support={len(supp)}, independent exact check: {ok} ({time.time()-t0:.1f}s)', flush=True)

if __name__ == '__main__':
    k = int(sys.argv[1])
    for n in [int(v) for v in sys.argv[2:]]: run(n, k)
