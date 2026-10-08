"""INDEPENDENT verification of facts F1-F6 of the P-PROOF all-n proof (no P-PROOF code imported).
Definitions (from the proof text): beta(x) = sum_{j>=0} (-1)^j/(x+j); a(K) = 4K^2 beta(K+1) + 1 - 2K;
omega(k) = sum_{y=k+1}^{2k} (-1)^y k/(y(y-1)) (rational); w(K) = (-1)^K omega(K+1).
 F1 a(K) > 0 (K>=1); F2 a(K) > a(K+1) (K>=1); F3 a(K)+a(K+1) <= 1/(2(K+1)) (K>=2);
 F4 w(K) > 0 and (K+1)(a(K)+a(K+1)) <= 4 w(K) (K>=2);
 F5 a1 - 2/21 - a3 > 0; a1 - 2/21 + a2 <= 2/7; a1 < 5/21;   F6 a3 < 1/20; a1 < 1/4.
Method (different from P-PROOF's):
 (a) K <= KS: rigorous interval arithmetic (mpmath.iv, 100 digits) with beta(K+1) = (-1)^K (ln2 - h_K), h_K exact.
 (b) K >= KS: own two-sided bounds for beta from a LONGER expansion u5 (5 terms) via the telescoping argument
     (d = u5 - beta, d(x)+d(x+1) = eps5(x); checked: eps5 has one sign and |eps5| decreasing => d between 0 and eps5),
     and omega(k) expressed through beta by an identity that I re-derive and check exactly; each fact becomes a
     rational-function inequality in K whose numerator is shown to have NO real root >= KS (Sturm, sympy count_roots)
     and to be positive at KS -- a different certificate than coefficient positivity."""
import sys
from fractions import Fraction as Fr
import sympy as sp
from mpmath import iv, mp

iv.dps = 100
LN2 = iv.log(2)

def beta_iv(K1):   # beta(K1) for integer K1 >= 1 via beta(m+1) = (-1)^m (ln2 - h_m)
    m = K1 - 1
    h = sum(Fr((-1) ** (i - 1), i) for i in range(1, m + 1))
    return (-1) ** m * (LN2 - iv.mpf(h.numerator) / h.denominator)

def a_iv(K):
    return 4 * K * K * beta_iv(K + 1) + 1 - 2 * K

def omega(k):
    return sum(Fr((-1) ** y * k, y * (y - 1)) for y in range(k + 1, 2 * k + 1))

def pos(ivx):   # rigorous: interval strictly > 0
    return ivx.a > 0

def nonneg(ivx):
    return ivx.a >= 0

KS = 60
ok = True
for K in range(1, KS + 1):
    aK, aK1 = a_iv(K), a_iv(K + 1)
    f1 = pos(aK); f2 = pos(aK - aK1)
    f3 = True if K < 2 else nonneg(iv.mpf(Fr(1, 2 * (K + 1)).numerator) / (2 * (K + 1)) - aK - aK1)
    if K >= 2:
        wK = (-1) ** K * omega(K + 1)
        f4 = wK > 0 and nonneg(4 * iv.mpf(wK.numerator) / wK.denominator - (K + 1) * (aK + aK1))
    else:
        f4 = True
    if not (f1 and f2 and f3 and f4):
        print('FAIL small K', K, f1, f2, f3, f4); ok = False
a1, a2, a3 = a_iv(1), a_iv(2), a_iv(3)
f5 = pos(a1 - iv.mpf(2) / 21 - a3) and nonneg(iv.mpf(2) / 7 - (a1 - iv.mpf(2) / 21 + a2)) and pos(iv.mpf(5) / 21 - a1)
f6 = pos(iv.mpf(1) / 20 - a3) and pos(iv.mpf(1) / 4 - a1)
print(f'(a) interval checks K = 1..{KS}: F1-F4 {ok};  F5 {f5};  F6 {f6}')
print(f'    a(1) in [{float(a1.a):.12f},{float(a1.b):.12f}] (= 3-4ln2 = {float(3 - 4 * LN2.a):.12f})')

# ---------- (b) large K ----------
x, K = sp.symbols('x K', positive=True)
u5 = 1 / (2 * x) + sp.Rational(1, 4) / x**2 - sp.Rational(1, 8) / x**4 + sp.Rational(1, 4) / x**6 - sp.Rational(17, 16) / x**8
eps5 = sp.factor(sp.together(u5 + u5.subs(x, x + 1) - 1 / x))
en, ed = sp.fraction(eps5)
dif = sp.factor(sp.together(eps5 - eps5.subs(x, x + 1)))
dn, dd = sp.fraction(dif)
def roots_ge(poly_expr, var, lo):
    P = sp.Poly(sp.expand(poly_expr), var)
    return P.count_roots(lo, sp.oo) if P.degree() > 0 else 0
# sign of eps5 and of its decrement on [KS, inf)
e_sign = sp.sign(sp.N((en / ed).subs(x, KS)))
e_ok = roots_ge(en, x, KS) == 0 and roots_ge(ed, x, KS) == 0
d_ok = roots_ge(dn, x, KS) == 0 and roots_ge(dd, x, KS) == 0 and sp.sign(sp.N((dn / dd).subs(x, KS))) == e_sign
print(f'(b) eps5 = {eps5};  sign on [{KS},inf): {e_sign}, no roots {e_ok};  |eps5| decreasing: {d_ok}')
# d = u5 - beta lies between 0 and eps5 (if eps5 < 0: eps5 <= d <= 0)
if e_sign > 0:
    b_lo = lambda y: u5.subs(x, y) - eps5.subs(x, y); b_hi = lambda y: u5.subs(x, y)
else:
    b_lo = lambda y: u5.subs(x, y); b_hi = lambda y: u5.subs(x, y) - eps5.subs(x, y)
# omega identity: omega(k) = sum_{y=k+1}^{2k} (-1)^y k (1/(y-1) - 1/y); re-derive: sum_{y=k+1}^{2k} (-1)^y/(y-1) = sum_{z=k}^{2k-1} (-1)^{z+1}/z,
# sum_{z>=m} (-1)^z / z = (-1)^m beta(m)  =>  omega(k)/k = -[(-1)^k beta(k) - (-1)^{2k} beta(2k)] - [(-1)^{k+1} beta(k+1) - (-1)^{2k+1} beta(2k+1)]
def omega_via_beta(k, beta):   # beta: function
    return k * (-((-1) ** k * beta(k) - beta(2 * k)) - ((-1) ** (k + 1) * beta(k + 1) + beta(2 * k + 1)))
mp.dps = 110
def beta_mp(K1):
    m = K1 - 1
    h = sum(Fr((-1) ** (i - 1), i) for i in range(1, m + 1))
    return (-1) ** m * (mp.log(2) - mp.mpf(h.numerator) / h.denominator)
bchk = all(abs(mp.mpf(omega(k).numerator) / omega(k).denominator - omega_via_beta(k, beta_mp)) < mp.mpf(10) ** -90 for k in range(2, 40))
print(f'    omega(k) = k[ -((-1)^k b(k) - b(2k)) - ((-1)^(k+1) b(k+1) + b(2k+1)) ] checked k=2..39 (100 digits): {bchk}')
# rewrite with beta(k)=1/k - beta(k+1), beta(2k+1) = 1/(2k) - beta(2k):
#   omega(k) = k[ -(-1)^k(1/k - beta(k+1)) + beta(2k) + (-1)^k beta(k+1) - 1/(2k) + beta(2k) ] = (-1)^k(2k beta(k+1) - 1) + 2k beta(2k) - 1/2
om_formula = lambda k, B1, B2: (-1) ** k * (2 * k * B1 - 1) + 2 * k * B2 - mp.mpf(1) / 2
ochk = all(abs(mp.mpf(omega(k).numerator) / omega(k).denominator - om_formula(k, beta_mp(k + 1), beta_mp(2 * k))) < mp.mpf(10) ** -90 for k in range(2, 40))
print(f'    omega(k) = (-1)^k (2k beta(k+1) - 1) + 2k beta(2k) - 1/2 checked k=2..39: {ochk}')

def lower_upper_a(Kv):   # symbolic bounds of a(K) = 4K^2 beta(K+1) + 1 - 2K
    return 4 * Kv**2 * b_lo(Kv + 1) + 1 - 2 * Kv, 4 * Kv**2 * b_hi(Kv + 1) + 1 - 2 * Kv
aL, aU = lower_upper_a(K); a1L, a1U = lower_upper_a(K + 1)
def show_pos(expr, name):
    num, den = sp.fraction(sp.factor(sp.together(expr)))
    okn = roots_ge(num, K, KS) == 0 and sp.N(num.subs(K, KS)) > 0
    okd = roots_ge(den, K, KS) == 0 and sp.N(den.subs(K, KS)) > 0
    print(f'    {name}: numerator deg {sp.Poly(num, K).degree()}, no roots >= {KS} and positive: {okn}; denominator ok: {okd}')
    return okn and okd
res = []
res.append(show_pos(aL, 'F1  a(K) > 0'))
res.append(show_pos(aL - a1U, 'F2  a(K) - a(K+1) > 0'))
res.append(show_pos(sp.Rational(1, 2) / (K + 1) - aU - a1U, 'F3  1/(2(K+1)) - a(K) - a(K+1) >= 0'))
# F4: w(K) = (-1)^K omega(K+1) = -(2(K+1) beta(K+2) - 1) + (-1)^K (2(K+1) beta(2K+2) - 1/2)
for par in (0, 1):
    s = 1 if par == 0 else -1
    # w = 1 - 2(K+1) beta(K+2) + s*(2(K+1) beta(2K+2) - 1/2); lower bound picks beta(K+2) upper, beta(2K+2) lower (s=+1) / upper (s=-1)
    wL = 1 - 2 * (K + 1) * b_hi(K + 2) + s * (2 * (K + 1) * (b_lo(2 * K + 2) if s > 0 else b_hi(2 * K + 2)) - sp.Rational(1, 2))
    res.append(show_pos(wL, f'F4  w(K) > 0      (K {"even" if par == 0 else "odd"})'))
    res.append(show_pos(4 * wL - (K + 1) * (aU + a1U), f'F4  4w - (K+1)(a(K)+a(K+1)) >= 0 (K {"even" if par == 0 else "odd"})'))
print(f'(b) all large-K facts for K >= {KS}: {all(res) and e_ok and d_ok and bchk and ochk}')
print('ALL COORDINATOR FACT CHECKS:', ok and f5 and f6 and all(res) and e_ok and d_ok and bchk and ochk)
