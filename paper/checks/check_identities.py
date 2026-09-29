"""Symbolic verification (sympy, exact rational arithmetic) of every algebraic identity stated in the
manuscript main.tex.  Each check prints OK/FAIL; the script exits with status 1 on any failure.

Covered:
  * Lemma B ingredients: eps(x) = u(x) + u(x+1) - 1/x, and eps(x) - eps(x+1) (closed forms).
  * sigma bounds:  c(x) = 2/(x(x+1)),  c(x)-c(x+1) = 4/(x(x+1)(x+2)) (and it is nonincreasing),
    c/2 = 1/(x(x+1)),  c/2 + (c(x)-c(x+1))/2 = (x+4)/(x(x+1)(x+2)).
  * a(K) = 2/(K+1) - 1 + K^2 sigma(K+1)  and  a(M) = 1 - M^2 sigma(M)  (beta, sigma treated as symbols
    subject to beta(x)+beta(x+1) = 1/x).
  * M^2 (M+5)/((M+1)(M+2)(M+3)) = 1 - 1/(M+1) - 6M/((M+1)(M+2)(M+3))   (Lemma sigma (v)).
  * omega identity in terms of beta (via the telescoping formula), checked symbolically for k <= 12 and
    the general proof steps.
  * w(K) formula from the omega identity.
  * The polynomial identities of Appendix A (F1, F2, F3, F4a-F4d) EXACTLY as in UnifFacts.lean,
    and positivity of all numerator/denominator coefficients.
  * Renewal square: H(l)-H(l+1), H(m+1) = 1/(K+1), W(l) = 2 (l <= m), W(m+1) = 1, sum_l H(l) = (m+1)^2/n.
  * Dipole: q_L(x+1) - q_L(x), window difference, Q(x+1)-Q(x) identity for symbolic alpha (all small
    K, M, x), tau(K+1) = 2/(K+1).
  * Hall identity  L_M = c_M [ (M+1)(1-Z)^2/Z + F_k ]  (symbolic in the gaps c_m).
"""
import sys
import sympy as sp

FAILS = []


def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond:
        FAILS.append(name)


x, K, M, k, t, al = sp.symbols('x K M k t alpha', positive=True)

# ---------------------------------------------------------------- Lemma B
u = 1 / (2 * x) + sp.Rational(1, 4) / x**2 - sp.Rational(1, 8) / x**4 + sp.Rational(1, 4) / x**6
eps = (17 * x**4 + 34 * x**3 + 29 * x**2 + 12 * x + 2) / (8 * x**6 * (x + 1)**6)
ok('Lemma B: u(x)+u(x+1)-1/x = eps(x)', sp.simplify(u + u.subs(x, x + 1) - 1 / x - eps) == 0)
deps = (17 * x**4 + 68 * x**3 + 100 * x**2 + 64 * x + 16) / (x**6 * (x + 1) * (x + 2)**6)
ok('Lemma B: eps(x)-eps(x+1) closed form', sp.simplify(eps - eps.subs(x, x + 1) - deps) == 0)

# ---------------------------------------------------------------- sigma bounds
c = 2 / (x * (x + 1))
dc = sp.simplify(c - c.subs(x, x + 1))
ok('c(x)-c(x+1) = 4/(x(x+1)(x+2))', sp.simplify(dc - 4 / (x * (x + 1) * (x + 2))) == 0)
ddc = sp.factor(sp.simplify(dc - dc.subs(x, x + 1)))
ok('(c(x)-c(x+1)) - (c(x+1)-c(x+2)) = 12/(x(x+1)(x+2)(x+3)) >= 0',
   sp.simplify(ddc - 12 / (x * (x + 1) * (x + 2) * (x + 3))) == 0)
ok('c/2 + dc/2 = (x+4)/(x(x+1)(x+2))', sp.simplify(c / 2 + dc / 2 - (x + 4) / (x * (x + 1) * (x + 2))) == 0)
# sigma strictly decreasing:  (x+1+4)/((x+1)(x+2)(x+3)) < 1/(x(x+1))  <=>  x(x+5) < (x+2)(x+3)
ok('sigma decreasing: (x+2)(x+3) - x(x+5) = 6', sp.expand((x + 2) * (x + 3) - x * (x + 5)) == 6)

# ---------------------------------------------------------------- a(K) in terms of sigma
b1, b2 = sp.symbols('b1 b2')        # b1 = beta(K+1); beta(K) = 1/K - b1 (not needed)
sig_K1 = 4 * b1 - 2 / (K + 1)      # sigma(K+1)
aK = 4 * K**2 * b1 + 1 - 2 * K
ok('a(K) = 2/(K+1) - 1 + K^2 sigma(K+1)', sp.simplify(2 / (K + 1) - 1 + K**2 * sig_K1 - aK) == 0)
# a(M) = 1 - M^2 sigma(M): sigma(M) = 4 beta(M) - 2/M, beta(M) = 1/M - beta(M+1)
bM1 = sp.symbols('bM1')
aM = 4 * M**2 * bM1 + 1 - 2 * M
sig_M = 4 * (1 / M - bM1) - 2 / M
ok('a(M) = 1 - M^2 sigma(M)', sp.simplify(1 - M**2 * sig_M - aM) == 0)
# sigma(x) + sigma(x+1) = 2/(x(x+1)) from beta(x)+beta(x+1) = 1/x
bx = sp.symbols('bx')
sx = 4 * bx - 2 / x
sx1 = 4 * (1 / x - bx) - 2 / (x + 1)
ok('sigma(x)+sigma(x+1) = 2/(x(x+1))', sp.simplify(sx + sx1 - 2 / (x * (x + 1))) == 0)

# ---------------------------------------------------------------- Lemma sigma (v)
lhs = M**2 * (M + 5) / ((M + 1) * (M + 2) * (M + 3))
rhs = 1 - 1 / (M + 1) - 6 * M / ((M + 1) * (M + 2) * (M + 3))
ok('M^2 (M+5)/((M+1)(M+2)(M+3)) = 1 - 1/(M+1) - 6M/(...)', sp.simplify(lhs - rhs) == 0)

# ---------------------------------------------------------------- omega identity (symbolic beta values)
# beta values as symbols B[j] with the relation B[j] + B[j+1] = 1/j; we express everything in terms of
# B[k+1] and B[2k] and check  omega(k) = (-1)^k (2k B[k+1] - 1) + 2k B[2k] - 1/2  for k = 1..12.
for kk in range(1, 13):
    Bk1, B2k = sp.symbols('Bk1 B2k')
    # beta(j) for j in [k, 2k+1] in terms of Bk1 (upwards and downwards) - but beta(2k) is independent of
    # beta(k+1) only through the relation chain; the chain gives beta(2k) = +-Bk1 + rational, so we use the
    # chain for all and keep Bk1 as the only symbol.
    beta = {kk + 1: Bk1}
    for j in range(kk + 1, 2 * kk + 1):
        beta[j + 1] = sp.Rational(1, j) - beta[j]
    beta[kk] = sp.Rational(1, kk) - beta[kk + 1]
    omega = sum(sp.Rational((-1)**y * kk, y * (y - 1)) for y in range(kk + 1, 2 * kk + 1))
    formula = (-1)**kk * (2 * kk * beta[kk + 1] - 1) + 2 * kk * beta[2 * kk] - sp.Rational(1, 2)
    ok(f'omega identity k={kk}', sp.simplify(formula - omega) == 0)

# ---------------------------------------------------------------- F1-F4 polynomial identities (Appendix A)
def uB(y):
    return 1 / (2 * y) + sp.Rational(1, 4) / y**2 - sp.Rational(1, 8) / y**4 + sp.Rational(1, 4) / y**6


def epsB(y):
    return (17 * y**4 + 34 * y**3 + 29 * y**2 + 12 * y + 2) / (8 * y**6 * (y + 1)**6)


def aUp(KK):
    return 4 * KK**2 * uB(KK + 1) + 1 - 2 * KK


def aLo(KK):
    return 4 * KK**2 * (uB(KK + 1) - epsB(KK + 1)) + 1 - 2 * KK


def wOddLo(KK):
    return sp.Rational(3, 2) - 2 * (KK + 1) * (uB(KK + 2) + uB(2 * KK + 2))


def wEvenLo(KK):
    return (sp.Rational(1, 2) - 2 * (KK + 1) * uB(KK + 2)
            + 2 * (KK + 1) * (uB(2 * KK + 2) - epsB(2 * KK + 2)))


P1n = K**5 + 13 * K**4 + 70 * K**3 + 194 * K**2 + 256 * K + 128
P1d = 2 * (K + 1) * (K + 2)**6
P2n = 2 * K**4 + 23 * K**3 + 101 * K**2 + 170 * K + 98
P2d = 2 * (K + 1) * (K + 2)**6
P3n = (k**12 + 41 * k**11 + 764 * k**10 + 8545 * k**9 + 63789 * k**8 + 334153 * k**7 + 1256064 * k**6
       + 3400638 * k**5 + 6544384 * k**4 + 8654345 * k**3 + 7354236 * k**2 + 3503150 * k + 660280)
P3d = 2 * (k + 3)**6 * (k + 4)**7
P4an = (48 * K**10 + 768 * K**9 + 5442 * K**8 + 22428 * K**7 + 59385 * K**6 + 105468 * K**5
        + 127292 * K**4 + 103200 * K**3 + 53840 * K**2 + 16320 * K + 2176)
P4ad = 128 * (K + 1)**5 * (K + 2)**6
P4bn = (16 * k**10 + 544 * k**9 + 8242 * k**8 + 73212 * k**7 + 421633 * k**6 + 1641880 * k**5
        + 4368048 * k**4 + 7817152 * k**3 + 8974576 * k**2 + 5940736 * k + 1710240)
P4bd = 32 * (k + 3)**6 * (k + 4)**6
P4cn = (160 * K**11 + 3200 * K**10 + 29012 * K**9 + 157296 * K**8 + 566317 * K**7 + 1420999 * K**6
        + 2535030 * K**5 + 3215114 * K**4 + 2841125 * K**3 + 1666285 * K**2 + 583870 * K + 92626)
P4cd = 4 * (K + 2)**6 * (2 * K + 3)**6
P4dn = (192 * k**16 + 10816 * k**15 + 285192 * k**14 + 4672168 * k**13 + 53227666 * k**12
        + 447135728 * k**11 + 2864967224 * k**10 + 14282437922 * k**9 + 55985185735 * k**8
        + 173131057544 * k**7 + 420984335806 * k**6 + 796458028404 * k**5 + 1149337523504 * k**4
        + 1223024950168 * k**3 + 905103455591 * k**2 + 416231111464 * k + 89613810730)
P4dd = 2 * (k + 3)**6 * (k + 4)**6 * (2 * k + 7)**6

ok('poly_F1:  aLo(K) = P1n/P1d', sp.simplify(aLo(K) - P1n / P1d) == 0)
ok('poly_F2:  aLo(K) - aUp(K+1) = P2n/P2d', sp.simplify(aLo(K) - aUp(K + 1) - P2n / P2d) == 0)
ok('poly_F3:  1/(2(K+1)) - aUp(K) - aUp(K+1) = P3n/P3d at K = k+2',
   sp.simplify(1 / (2 * ((k + 2) + 1)) - aUp(k + 2) - aUp(k + 3) - P3n / P3d) == 0)
ok('poly_F4a: wOddLo(K) = P4an/P4ad', sp.simplify(wOddLo(K) - P4an / P4ad) == 0)
ok('poly_F4b: 4 wOddLo(K)/(K+1) - aUp(K) - aUp(K+1) = P4bn/P4bd at K = k+2',
   sp.simplify(4 * wOddLo(k + 2) / (k + 3) - aUp(k + 2) - aUp(k + 3) - P4bn / P4bd) == 0)
ok('poly_F4c: wEvenLo(K) = P4cn/P4cd', sp.simplify(wEvenLo(K) - P4cn / P4cd) == 0)
ok('poly_F4d: 4 wEvenLo(K)/(K+1) - aUp(K) - aUp(K+1) = P4dn/P4dd at K = k+2',
   sp.simplify(4 * wEvenLo(k + 2) / (k + 3) - aUp(k + 2) - aUp(k + 3) - P4dn / P4dd) == 0)
for name, poly, var in [('P1n', P1n, K), ('P2n', P2n, K), ('P3n', P3n, k), ('P4an', P4an, K),
                        ('P4bn', P4bn, k), ('P4cn', P4cn, K), ('P4dn', P4dn, k)]:
    cs = sp.Poly(sp.expand(poly), var).all_coeffs()
    ok(f'{name}: all {len(cs)} coefficients positive (degree {len(cs) - 1})', all(cc > 0 for cc in cs))

# w(K) in terms of beta: from omega identity with k = K+1
bK2, b2K2 = sp.symbols('bK2 b2K2')
for par in (0, 1):
    sgn = (-1)**par
    omega_expr = (-sgn) * (2 * (K + 1) * bK2 - 1) + 2 * (K + 1) * b2K2 - sp.Rational(1, 2)  # (-1)^(K+1) = -sgn
    w_expr = sgn * omega_expr
    target = -(2 * (K + 1) * bK2 - 1) + sgn * (2 * (K + 1) * b2K2 - sp.Rational(1, 2))
    ok(f'w(K) formula (K parity {par})', sp.simplify(w_expr - target) == 0)
# wOddLo / wEvenLo come from these with the Lemma B bounds: odd: w = 3/2 - 2(K+1)(beta(K+2)+beta(2K+2))
ok('odd K: w = 3/2 - 2(K+1)(beta(K+2) + beta(2K+2))',
   sp.simplify((-(2 * (K + 1) * bK2 - 1) - (2 * (K + 1) * b2K2 - sp.Rational(1, 2)))
               - (sp.Rational(3, 2) - 2 * (K + 1) * (bK2 + b2K2))) == 0)
ok('even K: w = 1/2 - 2(K+1) beta(K+2) + 2(K+1) beta(2K+2)',
   sp.simplify((-(2 * (K + 1) * bK2 - 1) + (2 * (K + 1) * b2K2 - sp.Rational(1, 2)))
               - (sp.Rational(1, 2) - 2 * (K + 1) * bK2 + 2 * (K + 1) * b2K2)) == 0)

# ---------------------------------------------------------------- renewal square
n, m, l = sp.symbols('n m l', positive=True)
Kr = n - m - 1
H = lambda ll: 1 - Kr**2 / ((n - ll) * (n - ll + 1))
ok('renewal: H(l)-H(l+1) = 2K^2/((n-l-1)(n-l)(n-l+1))',
   sp.simplify(H(l) - H(l + 1) - 2 * Kr**2 / ((n - l - 1) * (n - l) * (n - l + 1))) == 0)
ok('renewal: H(m+1) = 1/(K+1)', sp.simplify(H(m + 1) - 1 / (Kr + 1)) == 0)
ok('renewal: W(l) = 2H(l) + (n-l-1)(H(l)-H(l+1)) = 2', sp.simplify(2 * H(l) + (n - l - 1) * (H(l) - H(l + 1)) - 2) == 0)
ok('renewal: W(m+1) = (n-m) H(m+1) = 1', sp.simplify((n - m) * H(m + 1) - 1) == 0)
ok('renewal: (m+1) - K^2 (1/(n-m-1) - 1/n) = (m+1)^2/n',
   sp.simplify((m + 1) - Kr**2 * (1 / (n - m - 1) - 1 / n) - (m + 1)**2 / n) == 0)
# numeric sum check for many (n, m)
allok = True
for nn in range(2, 40):
    for mm in range(0, nn - 1):
        KK = nn - mm - 1
        s_ = sum(1 - sp.Rational(KK * KK, (nn - ll) * (nn - ll + 1)) for ll in range(1, mm + 2))
        allok &= (s_ == sp.Rational((mm + 1)**2, nn))
ok('renewal: sum_{l=1}^{m+1} H(l) = (m+1)^2/n for all 2<=n<40, m<=n-2', allok)

# ---------------------------------------------------------------- dipole: Q differences, tau(K+1)
def qL(LL, xx):
    return (2 * xx * (xx - 1) - 2 * LL**2) if xx >= LL + 1 else 0


def Qf(KK, MM, a, xx):
    return qL(KK, xx) - qL(MM, xx) + (2 * (KK + 1) * a if KK + 2 <= xx <= 2 * KK + 2 else 0)


allok = True
for KK in range(1, 9):
    for MM in range(KK + 1, KK + 12):
        for xx in range(0, 40):
            lhs = sp.expand(Qf(KK, MM, al, xx + 1) - Qf(KK, MM, al, xx))
            I = lambda b: 1 if b else 0
            rhs = sp.expand(xx * (2 * I(xx >= KK) + 2 * I(xx >= KK + 1) - 2 * I(xx >= MM) - 2 * I(xx >= MM + 1)
                                  + 2 * al * I(xx == KK + 1) - al * I(xx == 2 * KK + 2)))
            allok &= (sp.simplify(lhs - rhs) == 0)
ok('Q(x+1)-Q(x) = x(2[x>=K]+2[x>=K+1]-2[x>=M]-2[x>=M+1]+2a[x=K+1]-a[x=2K+2]) (K<=8, M<K+12, x<40)', allok)
allok = True
for KK in range(1, 30):
    for MM in range(KK + 1, KK + 5):
        allok &= (sp.Rational(Qf(KK, MM, 0, KK + 1), (KK + 1) * KK) == sp.Rational(2, KK + 1))
ok('tau(K+1) = Q(K+1)/((K+1)K) = 2/(K+1)', allok)

# ---------------------------------------------------------------- Hall identity (symbolic gaps)
allok = True
for dd in range(2, 8):
    cs = sp.symbols(f'c0:{dd}', nonnegative=True)
    p = [sum(cs[mm] for mm in range(i, dd)) for i in range(dd)]           # p_i = sum_{m>=i} c_m
    for kk in range(0, dd):
        # p is nonincreasing, so B_i = min(p_i, p_k) = p_k for i <= k and p_i for i > k
        Bv = [(p[kk] if i <= kk else p[i]) for i in range(dd)]
        Z = sum(Bv)
        E = sum((mm + 1) * cs[mm] for mm in range(kk))
        Fk = sum((2 * i + 1) * (p[i] - p[kk]) for i in range(kk))
        ok_ZE = sp.expand(Z - sum((MM + 1) * cs[MM] for MM in range(kk, dd))) == 0
        # (I5): sum p - Z = E  (with the normalisation sum p = 1 this is 1 - Z = E)
        tot = sum(p)
        ok_E = sp.expand(tot - Z - E) == 0
        # Abel summation: sum_{m<k} (m+1)^2 c_m = F_k
        ok_F = sp.expand(sum((mm + 1)**2 * cs[mm] for mm in range(kk)) - Fk) == 0
        for MM in range(kk, dd):
            # homogeneous form of A_M = (1-Z^2)(M+1)c_M/Z with 1 replaced by tot = sum p
            AMh = (tot - Z) * (tot + Z) * (MM + 1) * cs[MM] / Z
            bM = sum(cs[mm] * cs[MM] * ((MM + 1)**2 - (MM - mm)**2) for mm in range(kk))
            LM = AMh - bM
            hall = cs[MM] * ((MM + 1) * E**2 / Z + Fk)
            allok &= (sp.simplify(LM - hall) == 0) and ok_ZE and ok_E and ok_F
ok('Hall identity L_M = c_M((M+1)E^2/Z + F_k) (homogeneous form, d<=7, all k, M)', allok)

print()
if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)
print('ALL IDENTITY CHECKS PASSED')
