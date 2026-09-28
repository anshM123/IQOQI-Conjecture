"""EXACT verification of every numeric inequality used in the P-PROOF all-n proof of UNIF(n,lo,hi).

beta(x) = sum_{j>=0} (-1)^j/(x+j)  (x > 0),  beta(x) + beta(x+1) = 1/x.
LEMMA B:  for every real x > 0:  u(x) - eps(x) <= beta(x) <= u(x), where
   u(x)   = 1/(2x) + 1/(4x^2) - 1/(8x^4) + 1/(4x^6),
   eps(x) = u(x) + u(x+1) - 1/x = (17x^4+34x^3+29x^2+12x+2) / (8 x^6 (x+1)^6)    [checked symbolically below]
 proof: d = u - beta satisfies d(x)+d(x+1) = eps(x), d -> 0, so d(x) = sum_j (-1)^j eps(x+j); eps > 0 and
 eps(x) - eps(x+1) > 0 (numerators with positive coefficients, checked below) => 0 <= d(x) <= eps(x).
Shifted evaluation (small arguments): beta(x) = sum_{j<m} (-1)^j/(x+j) + (-1)^m beta(x+m).

a(K) = 4K^2 beta(K+1) + 1 - 2K,   omega(k) = sum_{y=k+1}^{2k} (-1)^y k/(y(y-1))  (rational, exact),
omega(k) = (-1)^k (2k beta(k+1) - 1) + 2k beta(2k) - 1/2   [identity, checked exactly for k <= 60 below via ln2 cancel].

FACTS (all K in the stated ranges):
 F1  a(K) > 0                                   K >= 1
 F2  a(K) > a(K+1)                              K >= 1
 F3  a(K) + a(K+1) <= 1/(2(K+1))                K >= 2
 F4  w(K) := (-1)^K omega(K+1) > 0  and  (K+1)(a(K)+a(K+1)) <= 4 w(K)        K >= 2
 F5  (K = 1, alpha = 2/7):  a(1) - 2/21 - a(3) > 0;   a(1) - 2/21 + a(2) <= 2/7;   a(1) < 5/21
 F6  a(3) < 1/20;  a(1) < 1/4
Method: K < K0 exact rational interval evaluation (shifted Lemma B, all Fractions);
        K >= K0: the inequality with Lemma-B bounds inserted is a rational-function inequality; after clearing
        positive denominators the numerator polynomial P(K) is shown >= 0 on [K0, inf) by expanding P(K0 + t) and
        checking all coefficients are >= 0 (sympy, exact rationals)."""
import sys
from fractions import Fraction as F
import sympy as sp

x, t, Ks = sp.symbols('x t K', positive=True)
u_sym = 1 / (2 * x) + sp.Rational(1, 4) / x**2 - sp.Rational(1, 8) / x**4 + sp.Rational(1, 4) / x**6
eps_claim = (17 * x**4 + 34 * x**3 + 29 * x**2 + 12 * x + 2) / (8 * x**6 * (x + 1)**6)
REPORT = []

def rep(msg):
    print(msg, flush=True); REPORT.append(msg)

def poly_nonneg_from(expr_num, var, K0):
    """True if polynomial expr_num(var) has all coefficients >= 0 after var = K0 + t (so >= 0 on [K0, inf))."""
    P = sp.Poly(sp.expand(expr_num.subs(var, K0 + t)), t)
    cs = P.all_coeffs()
    return all(c >= 0 for c in cs) and any(c > 0 for c in cs)

def lemmaB_symbolic():
    eps = sp.simplify(u_sym + u_sym.subs(x, x + 1) - 1 / x - eps_claim)
    ok1 = (eps == 0)
    num = sp.Poly(sp.expand(17 * x**4 + 34 * x**3 + 29 * x**2 + 12 * x + 2), x)
    ok2 = all(c > 0 for c in num.all_coeffs())
    d = sp.factor(sp.together(eps_claim - eps_claim.subs(x, x + 1)))
    dn, dd = sp.fraction(d)
    cn = sp.Poly(sp.expand(dn), x).all_coeffs(); okn = all(c >= 0 for c in cn) and any(c > 0 for c in cn)
    cd = sp.Poly(sp.expand(dd), x).all_coeffs(); okd = all(c >= 0 for c in cd) and any(c > 0 for c in cd)
    rep(f'Lemma B: eps identity {ok1}; eps numerator positive coeffs {ok2}; eps(x)-eps(x+1) = {d}: num/den positive coeffs {okn and okd}')
    return ok1 and ok2 and okn and okd

# ---------- exact rational bounds ----------
def uF(y):
    y = F(y); return 1 / (2 * y) + F(1, 4) / y**2 - F(1, 8) / y**4 + F(1, 4) / y**6

def epsF(y):
    y = F(y); return (17 * y**4 + 34 * y**3 + 29 * y**2 + 12 * y + 2) / (8 * y**6 * (y + 1)**6)

def beta_iv(xv, m=None):
    """rational interval [lo, hi] containing beta(xv) (xv positive integer or Fraction)."""
    if m is None:
        m = max(0, 60 - int(xv))
    head = sum((F((-1) ** j) / (xv + j) for j in range(m)), F(0))
    y = F(xv) + m
    lo_, hi_ = uF(y) - epsF(y), uF(y)
    if m % 2 == 0:
        return head + lo_, head + hi_
    return head - hi_, head - lo_

def a_iv(K):
    b = beta_iv(K + 1)
    return 4 * K * K * b[0] + 1 - 2 * K, 4 * K * K * b[1] + 1 - 2 * K

def omega(k):
    return sum((F((-1) ** y * k, y * (y - 1)) for y in range(k + 1, 2 * k + 1)), F(0))

def check_small(K0):
    ok = True
    for K in range(1, K0 + 2):
        aK, aK1 = a_iv(K), a_iv(K + 1)
        f1 = aK[0] > 0
        f2 = aK[0] > aK1[1]
        ok &= f1 and f2
        if not (f1 and f2): rep(f'  FAIL F1/F2 at K={K}')
        if K >= 2:
            f3 = aK[1] + aK1[1] <= F(1, 2 * (K + 1))
            w = (-1) ** K * omega(K + 1)
            f4 = w > 0 and (K + 1) * (aK[1] + aK1[1]) <= 4 * w
            ok &= f3 and f4
            if not (f3 and f4): rep(f'  FAIL F3/F4 at K={K}')
    rep(f'small K = 1..{K0+1}: F1, F2 (K>=1), F3, F4 (K>=2) exact interval checks: {ok}')
    return ok

def omega_identity_check(kmax=60):
    """omega(k) = (-1)^k (2k beta(k+1) - 1) + 2k beta(2k) - 1/2: both sides are rational + c*ln2 with the ln2 parts
    cancelling; check with interval enclosures (width ~1e-100) that the interval contains the exact rational omega(k)."""
    ok = True
    for k in range(1, kmax + 1):
        b1 = beta_iv(k + 1, m=200); b2 = beta_iv(2 * k, m=200)
        s = (-1) ** k
        lo1 = s * (2 * k * (b1[0] if s > 0 else b1[1]) - 1) + 2 * k * b2[0] - F(1, 2)
        hi1 = s * (2 * k * (b1[1] if s > 0 else b1[0]) - 1) + 2 * k * b2[1] - F(1, 2)
        w = omega(k)
        ok &= (lo1 <= w <= hi1)
    rep(f'omega identity check k=1..{kmax} (interval contains exact omega): {ok}')
    return ok

def symbolic_large(K0):
    y = sp.Symbol('y', positive=True)
    u = lambda z: 1 / (2 * z) + sp.Rational(1, 4) / z**2 - sp.Rational(1, 8) / z**4 + sp.Rational(1, 4) / z**6
    e = lambda z: (17 * z**4 + 34 * z**3 + 29 * z**2 + 12 * z + 2) / (8 * z**6 * (z + 1)**6)
    K = Ks
    ap = lambda k: 4 * k**2 * u(k + 1) + 1 - 2 * k                 # upper bound of a(k)
    am = lambda k: 4 * k**2 * (u(k + 1) - e(k + 1)) + 1 - 2 * k    # lower bound of a(k)
    k = K + 1
    w_odd = sp.Rational(3, 2) - 2 * k * (u(k + 1) + u(2 * k))              # K odd  (k even): lower bound of w(K)
    w_even = sp.Rational(1, 2) - 2 * k * u(k + 1) + 2 * k * (u(2 * k) - e(2 * k))   # K even (k odd)
    tests = {
        'F1  a(K) > 0': am(K),
        'F2  a(K) - a(K+1) > 0': am(K) - ap(K + 1),
        'F3  1/(2(K+1)) - a(K) - a(K+1) >= 0': sp.Rational(1, 2) / (K + 1) - ap(K) - ap(K + 1),
        'F4a (K odd)  w > 0': w_odd,
        'F4b (K odd)  4w/(K+1) - a(K) - a(K+1) >= 0': 4 * w_odd / (K + 1) - ap(K) - ap(K + 1),
        'F4c (K even) w > 0': w_even,
        'F4d (K even) 4w/(K+1) - a(K) - a(K+1) >= 0': 4 * w_even / (K + 1) - ap(K) - ap(K + 1),
    }
    ok = True
    for name, ex in tests.items():
        num, den = sp.fraction(sp.together(sp.simplify(ex)))
        num = sp.expand(num); den = sp.expand(den)
        # make denominator positive on K >= K0 (all coefficients positive after shift) and numerator >= 0
        dP = sp.Poly(sp.expand(den.subs(K, K0 + t)), t).all_coeffs()
        if all(c <= 0 for c in dP):
            num, den = -num, -den
            dP = [-c for c in dP]
        dpos = all(c >= 0 for c in dP) and any(c > 0 for c in dP)
        npos = poly_nonneg_from(num, K, K0)
        rep(f'  K >= {K0}: {name}: denominator>0 {dpos}, numerator>=0 {npos}  (deg num {sp.Poly(num, K).degree()})')
        ok &= dpos and npos
    return ok

def k1_facts():
    a1, a2, a3 = a_iv(1), a_iv(2), a_iv(3)
    al = F(2, 7)
    i_ = a1[0] - al / 3 - a3[1] > 0
    ii = a1[1] - al / 3 + a2[1] <= al
    iii = a1[1] < F(5, 21)
    f6 = a3[1] < F(1, 20) and a1[1] < F(1, 4)
    rep(f'F5 (K=1, alpha=2/7): (i) a1-2/21-a3>0 {i_} [value >= {float(a1[0]-al/3-a3[1]):.6f}], (ii) a1-2/21+a2<=2/7 {ii} '
        f'[slack >= {float(al-(a1[1]-al/3+a2[1])):.6f}], (iii) a1<5/21 {iii} [slack >= {float(F(5,21)-a1[1]):.6f}];  F6 a3<1/20, a1<1/4: {f6}')
    rep(f'   enclosures: a(1) in [{float(a1[0]):.12f},{float(a1[1]):.12f}], a(2) in [{float(a2[0]):.12f},{float(a2[1]):.12f}], a(3) in [{float(a3[0]):.12f},{float(a3[1]):.12f}]')
    return i_ and ii and iii and f6

if __name__ == '__main__':
    K0 = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    ok = lemmaB_symbolic()
    ok &= omega_identity_check()
    ok &= check_small(K0)
    ok &= symbolic_large(K0)
    ok &= k1_facts()
    rep(f'ALL FACTS VERIFIED: {ok}')
