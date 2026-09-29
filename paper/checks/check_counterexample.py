"""Verification of the counterexample to the strong majorisation form (Proposition in Section "Remarks" of main.tex).

Family (d >= 4):  delta = 1/(5d), eps = 2 delta^2, p = (1 - delta - (d-2) eps, delta, eps, ..., eps)  (d-2 copies),
                  s = 1 - p_0 = delta + (d-2) eps,   q = (p_0, s/(d-1), ..., s/(d-1)).
Claims checked EXACTLY (Fractions) for d = 4..400:
  (a) p is strictly positive, nonincreasing, sums to 1; q is nonincreasing and q < p (majorised);
  (b) the 2d-1 largest entries of p (x) p are p0^2 > p0 delta = p0 delta > p0 eps = ... = p0 eps (2(d-2) copies),
      and every other entry is <= delta^2 < p0 eps  (strict gaps at positions 1|2 and 2d-1|2d);
  (c) 2 lambda_1 + lambda_2 + ... + lambda_{2d-1} = 2 p0  (von Neumann bound is attained by q_0 = p_0 on both sides);
  (d) the key inequality  p0 eps + s^2 < s/(d-1)  (so the smallest eigenvalue of Y + Z cannot equal s/(d-1));
  also the explicit d = 4 numbers of the research report (p = (0.94, 0.05, 0.005, 0.005), bound 0.0083 < 0.02).
Numerical sanity check of the interlacing step (numpy): for random states rho with the forced block structure
  (rho = lambda_1 |00><00| + rho_O + rho_R with the prescribed spectra), the (d-1)x(d-1) block Y + Z of rho_A
  always has third eigenvalue <= p0 eps + s^2 < s/(d-1).
"""
import sys
from fractions import Fraction as F
import numpy as np

FAILS = []


def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond:
        FAILS.append(name)


def family(d):
    delta = F(1, 5 * d)
    eps = 2 * delta * delta
    p0 = 1 - delta - (d - 2) * eps
    p = [p0, delta] + [eps] * (d - 2)
    s = delta + (d - 2) * eps
    q = [p0] + [s / (d - 1)] * (d - 1)
    return p, q, delta, eps, s


allA = allB = allC = allD = True
worst_ratio = F(0)
for d in range(4, 401):
    p, q, delta, eps, s = family(d)
    p0 = p[0]
    # (a)
    allA &= all(x > 0 for x in p) and all(p[i] >= p[i + 1] for i in range(d - 1)) and sum(p) == 1
    allA &= all(q[i] >= q[i + 1] for i in range(d - 1)) and sum(q) == 1
    pp = sq = F(0)
    for i in range(d):
        pp += p[i]
        sq += q[i]
        allA &= sq <= pp
    # (b)
    lam = sorted((p[i] * p[j] for i in range(d) for j in range(d)), reverse=True)
    top = [p0 * p0] + [p0 * delta] * 2 + [p0 * eps] * (2 * (d - 2))
    allB &= lam[:2 * d - 1] == top
    allB &= lam[0] > lam[1] and lam[2 * d - 2] > lam[2 * d - 1]
    allB &= max(lam[2 * d - 1:]) == delta * delta and delta * delta < p0 * eps
    # (c)
    allC &= 2 * lam[0] + sum(lam[1:2 * d - 1]) == 2 * p0
    allC &= sum(lam[2 * d - 1:]) == s * s
    # (d)
    lhs, rhs = p0 * eps + s * s, s / (d - 1)
    allD &= lhs < rhs
    worst_ratio = max(worst_ratio, lhs / rhs)
ok('(a) p positive, sorted, normalised; q sorted, normalised, q majorised by p  (d = 4..400)', allA)
ok('(b) spectrum of p(x)p: top 2d-1 values p0^2, p0 delta x2, p0 eps x2(d-2); strict gaps; rest <= delta^2', allB)
ok('(c) 2 lambda_1 + lambda_2 + ... + lambda_{2d-1} = 2 p0 and the remaining mass is s^2', allC)
ok(f'(d) p0 eps + s^2 < s/(d-1)  (max ratio lhs/rhs = {float(worst_ratio):.4f})', allD)

# d = 4 explicit numbers
p, q, delta, eps, s = family(4)
ok('d = 4: p = (0.94, 0.05, 0.005, 0.005), q = (0.94, 0.02, 0.02, 0.02), p0 eps + s^2 = 0.0083 < 0.02',
   p == [F(94, 100), F(5, 100), F(5, 1000), F(5, 1000)] and q == [F(94, 100)] + [F(2, 100)] * 3
   and p[0] * eps + s * s == F(83, 10000) and s / 3 == F(2, 100))

# with delta fixed to 0.05 (as in the research report) and eps-padding, the bound fails for large d:
bad = [d for d in range(4, 30)
       if not (F(94, 100) * 0 + (1 - F(1, 20) - (d - 2) * F(1, 200)) * F(1, 200)
               + (F(1, 20) + (d - 2) * F(1, 200))**2 < (F(1, 20) + (d - 2) * F(1, 200)) / (d - 1))]
print('   (note) with delta = 0.05, eps = 0.005 fixed and eps-padding, the inequality (d) fails for d in', bad[:5], '...')

# with ZERO-padding (p = (1-delta-2eps, delta, eps, eps, 0, ..., 0)) the von Neumann bound is no longer attained
# at q_0 = p_0 for d >= 5 (extra positive products enter the top 2d-1 eigenvalues), so the argument does not apply:
zp_bad = []
for d in range(5, 12):
    de, ep = F(1, 20), F(1, 200)
    pz = [1 - de - 2 * ep, de, ep, ep] + [F(0)] * (d - 4)
    lamz = sorted((pz[i] * pz[j] for i in range(d) for j in range(d)), reverse=True)
    vn = 2 * lamz[0] + sum(lamz[1:2 * d - 1])
    if vn > 2 * pz[0]:
        zp_bad.append(d)
ok('zero-padded family: von Neumann maximum exceeds 2 p0 for d = 5..11 (argument of the report does not apply)',
   zp_bad == list(range(5, 12)))

# numerical sanity check of the interlacing/Weyl step
rng = np.random.default_rng(11)


def haar(nn):
    zz = (rng.normal(size=(nn, nn)) + 1j * rng.normal(size=(nn, nn))) / np.sqrt(2)
    qq, rr = np.linalg.qr(zz)
    return qq * (np.diag(rr) / np.abs(np.diag(rr)))


allN = True
for d in (4, 5, 6, 8):
    p, q, delta, eps, s = family(d)
    pf = [float(x) for x in p]
    p0 = pf[0]
    specO = [p0 * pf[1]] * 2 + [p0 * pf[2]] * (2 * (d - 2))
    specR = [pf[i] * pf[j] for i in range(1, d) for j in range(1, d)]
    for _ in range(200):
        VO = haar(2 * (d - 1))
        rhoO = VO @ np.diag(specO) @ VO.conj().T          # on O = span{|0j>} (+) span{|j0>}, j >= 1
        VR = haar((d - 1)**2)
        rhoR = VR @ np.diag(specR) @ VR.conj().T          # on R = span{|ij>}, i, j >= 1
        Y = rhoO[d - 1:, d - 1:]                          # compression to span{|j0>} (A-side vectors |j>)
        Zm = np.zeros((d - 1, d - 1), dtype=complex)      # Tr_B rho_R
        R4 = rhoR.reshape(d - 1, d - 1, d - 1, d - 1)
        for b in range(d - 1):
            Zm += R4[:, b, :, b]
        ev = np.sort(np.linalg.eigvalsh(Y + Zm))[::-1]
        allN &= ev[2] <= p0 * pf[2] + float(s * s) + 1e-12
        allN &= ev[-1] < float(s / (d - 1))
ok('numerical: lambda_3(Y+Z) <= p0 eps + s^2 < s/(d-1) for random block-structured states (d = 4,5,6,8)', allN)

# d = 3 example (Remark in Section 11): p = (0.4, 0.35, 0.25).  Mixing the three cells (1,1), (0,2), (2,0)
# (distinct rows and columns) to the diagonal x = (x11, x02, x20) = (0.1075, 0.1075, 0.1075), which is majorised by
# (p1^2, p0 p2, p2 p0) = (0.1225, 0.1, 0.1), gives both marginals q = (0.4075, 0.335, 0.2575), and q_0 > p_0.
p3 = [F(4, 10), F(35, 100), F(25, 100)]
Fm = [[p3[i] * p3[j] for j in range(3)] for i in range(3)]
t = F(1075, 10000)
Fm[1][1] = Fm[0][2] = Fm[2][0] = t
lamLC = sorted([p3[1] * p3[1], p3[0] * p3[2], p3[2] * p3[0]], reverse=True)
xLC = sorted([t, t, t], reverse=True)
majLC = sum(xLC) == sum(lamLC) and all(sum(xLC[:j]) <= sum(lamLC[:j]) for j in range(1, 4))
rowsA = [sum(Fm[i][j] for j in range(3)) for i in range(3)]
rowsB = [sum(Fm[i][j] for i in range(3)) for j in range(3)]
ok('d = 3 example: LC mixing is majorised, both marginals = (0.4075, 0.335, 0.2575), q_0 > p_0',
   majLC and rowsA == rowsB == [F(4075, 10000), F(335, 1000), F(2575, 10000)] and rowsA[0] > p3[0])

print()
if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)
print('ALL COUNTEREXAMPLE CHECKS PASSED')
