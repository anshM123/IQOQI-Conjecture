"""EXACT two-dipole construction: hooks a <= A image kernel; A < a <= n-2: T = img + c1 w1 + c2 w2 (dipoles at a, a-1),
H = T - c1 e_a - c2 e_{a-1}, G = c1[u<=2a-n-1] + c2[u<=2a-n-3]; top hook = residual.  c's: float LP vertex ->
exact rational solve on active constraints -> exact verification -> certificate + INDEPENDENT checker."""
import sys, os, time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from sympy import QQ
from sympy.polys.matrices import DomainMatrix
from imgkernel import kernel
sys.path.insert(0, os.path.join('..', 'stu3'))
from coord_check_hook import check as indep_check

def mp(n, x): return min(x + 1, 2 * n - 1 - x)

def rec(n, a, rhs):
    T = {}
    for s in range(a, -1, -1):
        acc = sum(T.get(t, 0) for t in range(s + 1, a + 1, 2))
        T[s] = (rhs(s) - 2 * acc) / (n - s)
    return T

def cellvals(n, a, T, H, G):
    out = {}
    for s in range(a + 1):
        for p in range(n - s):
            i, j = p, p + s
            v = T.get(s, 0) + (G.get(s, 0) if i + j == n - 1 else H.get(mp(n, i + j), 0))
            out[(s, p)] = v / 2
    return out

def run(n, seed=0):
    t0 = time.time()
    A = (n - 1) // 2
    cells = [(s, p) for s in range(n) for p in range(n - s)]
    base = {c: F(0) for c in cells}
    Y0 = {}
    for a in range(n - 1):
        K = kernel(n, a)
        Y0[a] = cellvals(n, a, K, {t: K.get(t, F(0)) for t in range(1, a + 1)}, {})
    mids = list(range(A + 1, n - 1))
    var = []; Y1 = {}
    for a in mids:
        for t in (a, a - 1):
            if not (2 * t > n - 1 and t <= a): continue
            D = {t: F(1)}
            rhs = lambda s, t=t, a=a: F(2) + (2 if (t > s and (t - s) % 2 == 1) else 0) - (1 if ((n - s) % 2 == 1 and s <= 2 * t - n - 1) else 0)
            Tt = rec(n, a, lambda s, t=t: F(2 if (t > s and (t - s) % 2 == 1) else 0) - F(1 if ((n - s) % 2 == 1 and s <= 2 * t - n - 1) else 0))
            Ht = {tt: Tt.get(tt, F(0)) - (1 if tt == t else 0) for tt in range(1, a + 2)}
            Gt = {u: F(1 if u <= 2 * t - n - 1 else 0) for u in range((n - 1) % 2, a + 1, 2)}
            var.append((a, t)); Y1[len(var) - 1] = cellvals(n, a, Tt, Ht, Gt)
    nv = len(var)
    # constraints  const + sum coef*c >= 0
    cons = []
    for a in mids:
        js = [j for j in range(nv) if var[j][0] == a]
        for c in Y0[a]:
            cons.append((Y0[a][c], {j: Y1[j][c] for j in js if Y1[j].get(c, 0) != 0}))
        j1 = [j for j in js if var[j][1] == a]; j2 = [j for j in js if var[j][1] == a - 1]
        if j1: cons.append((F(0), {j1[0]: F(1)}))
        if j1 and j2: cons.append((F(0), {j1[0]: F(1), j2[0]: F(1)}))
    for c in cells:
        const = 1 - sum(Y0[a].get(c, F(0)) for a in range(n - 1))
        cons.append((const, {j: -Y1[j][c] for j in range(nv) if Y1[j].get(c, 0) != 0}))
    cons = [(k0, d) for (k0, d) in cons if d or k0 != 0]
    for k0, d in cons:
        if not d: assert k0 >= 0, 'structurally negative'
    cons = [(k0, d) for (k0, d) in cons if d]
    Aub = np.zeros((len(cons), nv)); bub = np.zeros(len(cons))
    for i, (k0, d) in enumerate(cons):
        for j, v in d.items(): Aub[i, j] = -float(v)
        bub[i] = float(k0)
    rng = np.random.default_rng(seed + n)
    res = linprog(rng.uniform(-1, 1, nv), A_ub=Aub, b_ub=bub, bounds=[(-10, 10)] * nv, method='highs-ds')
    assert res.status == 0, res.message
    slack = bub - Aub @ res.x
    act = [i for i in range(len(cons)) if slack[i] < 1e-9]
    M = DomainMatrix([[QQ(-cons[i][1].get(j, F(0)).numerator, cons[i][1].get(j, F(0)).denominator) if cons[i][1].get(j, 0) != 0 else QQ(0)
                       for j in range(nv)] + [QQ(cons[i][0].numerator, cons[i][0].denominator)] for i in act],
                     (len(act), nv + 1), QQ)
    rref, piv = M.rref(); piv = list(piv)
    assert nv not in piv
    if len(piv) < nv:
        return f'n={n}: degenerate vertex (rank {len(piv)} < {nv})'
    rr = rref.to_Matrix()
    cval = [F(0)] * nv
    for ri, cj in enumerate(piv):
        v = rr[ri, nv]; cval[cj] = F(int(v.p), int(v.q))
    for k0, d in cons:
        assert k0 + sum(v * cval[j] for j, v in d.items()) >= 0, 'exact check failed'
    # assemble all hooks and certificate
    tot = {c: F(0) for c in cells}; x = {}
    for a in range(n - 1):
        vals = dict(Y0[a])
        for j in range(nv):
            if var[j][0] == a:
                for c, v in Y1[j].items(): vals[c] = vals.get(c, F(0)) + cval[j] * v
        for (s, p), v in vals.items():
            tot[(s, p)] += v
            if v != 0: x[(a, s, p)] = v
    for (s, p) in cells:
        v = 1 - tot[(s, p)]
        if v != 0: x[(n - 1, s, p)] = v
    assert all(v >= 0 for v in x.values())
    path = f'certs/dip2_n{n}.txt'
    with open(path, 'w') as f:
        f.write(f'# exact hook decomposition of the {n}-box: image kernels a<={A}, two-dipole hooks a<={n-2}, top hook = residual\n')
        for (a, s, p), v in sorted(x.items()): f.write(f'{a} {s} {p} {v}\n')
    ok = indep_check(n, path)
    return f'n={n}: {nv} dipole coefficients (exact rationals), independent exact check: {ok} ({time.time()-t0:.1f}s)'

if __name__ == '__main__':
    for n in [int(v) for v in sys.argv[1:]]:
        print(run(n), flush=True)
