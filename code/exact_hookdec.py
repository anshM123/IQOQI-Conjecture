"""EXACT rational hook decompositions of the n-box (certificates for the Uniformisation Lemma, p-independent).

A hook decomposition: x[a][s][i] >= 0 (a = 0..n-1 hooks, s = 0..a runs, i = 0..n-1-s positions) with
   (run)   sum_i x[a][s][i] = 1                              for all a, s <= a
   (rows)  x[a][0][r] + sum_{1<=s<=a} ( x[a][s][r] [r<=n-1-s] + x[a][s][r-s] [r>=s] ) = (2a+1)/n   for all a, r
   (cells) sum_{a>=s} x[a][s][i] = 1                          for all s, i
Method: HiGHS simplex vertex -> support -> exact rational solve (sympy DomainMatrix over QQ) -> exact check.
Writes hookdec_n{n}.txt (exact fractions) and prints a verification line."""
import sys, time
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from sympy import QQ
from sympy.polys.matrices import DomainMatrix


def build(n):
    idx = {}; nv = 0
    for a in range(n):
        for s in range(a + 1):
            for i in range(n - s):
                idx[(a, s, i)] = nv; nv += 1
    rows = []  # list of (dict var->coef, rhs Fraction)
    for a in range(n):
        for s in range(a + 1):
            rows.append(({idx[(a, s, i)]: 1 for i in range(n - s)}, Fr(1)))
        for r in range(n):
            dct = {idx[(a, 0, r)]: 1}
            for s in range(1, a + 1):
                if r <= n - 1 - s:
                    dct[idx[(a, s, r)]] = dct.get(idx[(a, s, r)], 0) + 1
                if r >= s:
                    dct[idx[(a, s, r - s)]] = dct.get(idx[(a, s, r - s)], 0) + 1
            rows.append((dct, Fr(2 * a + 1, n)))
    for s in range(n):
        for i in range(n - s):
            rows.append(({idx[(a, s, i)]: 1 for a in range(s, n)}, Fr(1)))
    return idx, nv, rows


def exact_certificate(n, verbose=True):
    idx, nv, rows = build(n)
    R, C, V, b = [], [], [], []
    for k, (dct, rhs) in enumerate(rows):
        for j, v in dct.items():
            R.append(k); C.append(j); V.append(float(v))
        b.append(float(rhs))
    A = coo_matrix((V, (R, C)), shape=(len(rows), nv)).tocsr()
    rng = np.random.default_rng(n)
    c = rng.uniform(0, 1, nv)             # generic objective -> a vertex
    res = linprog(c, A_eq=A, b_eq=np.array(b), bounds=(0, None), method='highs-ds')
    assert res.status == 0, res.message
    supp = [j for j in range(nv) if res.x[j] > 1e-9]
    # exact solve on the support
    Mrows = []
    for dct, rhs in rows:
        Mrows.append([QQ(int(dct.get(j, 0))) for j in supp] + [QQ(rhs.numerator, rhs.denominator)])
    M = DomainMatrix(Mrows, (len(rows), len(supp) + 1), QQ)
    rref, piv = M.rref()
    piv = list(piv)
    assert len(supp) not in piv, "inconsistent"
    assert len(piv) == len(supp), f"support not independent ({len(piv)} < {len(supp)})"
    rr = rref.to_Matrix()
    y = {}
    for r_i, col in enumerate(piv):
        val = rr[r_i, len(supp)]
        y[supp[col]] = Fr(int(val.p), int(val.q))
    x = [Fr(0)] * nv
    for j, v in y.items():
        x[j] = v
    # exact verification of every constraint and of nonnegativity
    ok = all(v >= 0 for v in x)
    for dct, rhs in rows:
        if sum(Fr(cf) * x[j] for j, cf in dct.items()) != rhs:
            ok = False; break
    return ok, x, idx


if __name__ == "__main__":
    for n in [int(a) for a in sys.argv[1:]] or list(range(1, 11)):
        t0 = time.time()
        ok, x, idx = exact_certificate(n)
        den = max(v.denominator for v in x)
        with open(f"hookdec_n{n}.txt", "w") as f:
            f.write(f"# exact hook decomposition of the {n}-box: a s i value\n")
            for (a, s, i), j in sorted(idx.items()):
                if x[j] != 0:
                    f.write(f"{a} {s} {i} {x[j]}\n")
        print(f"n={n}: exact hook decomposition verified={ok}; nonzeros={sum(1 for v in x if v != 0)}; "
              f"max denominator={den} ({time.time()-t0:.1f}s)", flush=True)
