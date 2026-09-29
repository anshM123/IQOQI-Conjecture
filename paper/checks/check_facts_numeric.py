"""High-precision numerical cross-checks (mpmath, 60 digits) and exact rational enclosures of every
numerical statement about the special functions in main.tex (Section "Special functions and the facts F1-F6").

These are CORROBORATION only: the proofs in the paper (and in Lean, UnifFacts.lean) are for all K.
Checks:
  * beta(x) = (psi((x+1)/2) - psi(x/2))/2 equals the alternating series and satisfies Lemma B, x = 1..3000.
  * beta(m+1) = (-1)^m (ln 2 - h_m) and a(1) = 3 - 4 ln 2, a(2) = 16 ln 2 - 11, a(3) = 25 - 36 ln 2.
  * sigma: sigma(x)+sigma(x+1) = 2/(x(x+1)), 1/(x(x+1)) <= sigma(x) <= (x+4)/(x(x+1)(x+2)), decreasing.
  * F1-F6 for K up to 3000 (F1, F2 from K = 0), and the consequence a(K) < 1/(2(K+1)).
  * the omega identity for k = 1..300 and w(K) > 0.
  * EXACT rational enclosures of a(1), a(2), a(3) from Lemma B at x = 2, 3, 4 and the decimal bounds
    0.227 < a(1) < 0.2344, 0.0901 < a(2) < 0.092, 0.0466 < a(3) < 0.0472 used in Lean (aF_one_bounds etc.).
  * alpha*(K, M) in (0, 2/(K+1)] for 2 <= K <= 150, K+1 <= M <= K+150.
  * asymptotics a(K) (K+1)^2 -> 1/2 (remark only).
"""
import sys
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 60
FAILS = []


def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond:
        FAILS.append(name)


def beta(x):
    x = mp.mpf(x)
    return (mp.digamma((x + 1) / 2) - mp.digamma(x / 2)) / 2


def beta_series(x, terms=4000):
    # alternating series with Euler-type acceleration via mpmath nsum
    return mp.nsum(lambda j: (-1)**int(j) / (x + j), [0, mp.inf])


def u(x):
    x = mp.mpf(x)
    return 1 / (2 * x) + 1 / (4 * x**2) - 1 / (8 * x**4) + 1 / (4 * x**6)


def eps(x):
    x = mp.mpf(x)
    return (17 * x**4 + 34 * x**3 + 29 * x**2 + 12 * x + 2) / (8 * x**6 * (x + 1)**6)


def sigma(x):
    return 4 * beta(x) - mp.mpf(2) / x


def a(K):
    return 4 * K * K * beta(K + 1) + 1 - 2 * K


def omega(k):
    return sum(mp.mpf((-1)**y * k) / (y * (y - 1)) for y in range(k + 1, 2 * k + 1))


def w(K):
    return (-1)**K * omega(K + 1)


# ---------------------------------------------------------------- beta
ok('beta digamma formula = alternating series (x = 1..20)',
   all(abs(beta(x) - beta_series(x)) < mp.mpf(10)**-40 for x in range(1, 21)))
ok('beta(1) = ln 2', abs(beta(1) - mp.log(2)) < mp.mpf(10)**-50)
ok('beta(x)+beta(x+1) = 1/x, x = 1..500', all(abs(beta(x) + beta(x + 1) - mp.mpf(1) / x) < mp.mpf(10)**-50
                                             for x in range(1, 501)))
ok('0 <= beta(x) <= 1/x, x = 1..500', all(0 <= beta(x) <= mp.mpf(1) / x for x in range(1, 501)))
ok('Lemma B: u - eps <= beta <= u for x = 1..3000',
   all(u(x) - eps(x) <= beta(x) <= u(x) for x in range(1, 3001)))
h = lambda mm: sum(mp.mpf((-1)**(i - 1)) / i for i in range(1, mm + 1))
ok('beta(m+1) = (-1)^m (ln 2 - h_m), m = 0..60',
   all(abs(beta(mm + 1) - (-1)**mm * (mp.log(2) - h(mm))) < mp.mpf(10)**-45 for mm in range(0, 61)))
ok('a(1) = 3 - 4 ln 2', abs(a(1) - (3 - 4 * mp.log(2))) < mp.mpf(10)**-50)
ok('a(2) = 16 ln 2 - 11', abs(a(2) - (16 * mp.log(2) - 11)) < mp.mpf(10)**-50)
ok('a(3) = 25 - 36 ln 2', abs(a(3) - (25 - 36 * mp.log(2))) < mp.mpf(10)**-50)
print('   a(1) =', mp.nstr(a(1), 15), ' a(2) =', mp.nstr(a(2), 15), ' a(3) =', mp.nstr(a(3), 15))

# ---------------------------------------------------------------- sigma
ok('sigma(x)+sigma(x+1) = 2/(x(x+1)), x=1..500',
   all(abs(sigma(x) + sigma(x + 1) - mp.mpf(2) / (x * (x + 1))) < mp.mpf(10)**-50 for x in range(1, 501)))
ok('1/(x(x+1)) <= sigma(x) <= (x+4)/(x(x+1)(x+2)), x = 1..3000',
   all(mp.mpf(1) / (x * (x + 1)) <= sigma(x) <= mp.mpf(x + 4) / (x * (x + 1) * (x + 2)) for x in range(1, 3001)))
ok('sigma strictly decreasing, x = 1..3000', all(sigma(x + 1) < sigma(x) for x in range(1, 3001)))
ok('sigma(4) <= 1/15, sigma(5) <= 3/70 (Lemma bounds, case D)',
   sigma(4) <= mp.mpf(1) / 15 and sigma(5) <= mp.mpf(3) / 70 and
   F(4 + 4, 4 * 5 * 6) == F(1, 15) and F(5 + 4, 5 * 6 * 7) == F(3, 70))
ok('a(K) = 2/(K+1) - 1 + K^2 sigma(K+1), K = 0..500',
   all(abs(a(K) - (mp.mpf(2) / (K + 1) - 1 + K * K * sigma(K + 1))) < mp.mpf(10)**-45 for K in range(0, 501)))
ok('a(M) = 1 - M^2 sigma(M), M = 1..500',
   all(abs(a(M) - (1 - M * M * sigma(M))) < mp.mpf(10)**-45 for M in range(1, 501)))
ok('M^2 sigma(M+1) <= 1 - 1/(M+1), M = 1..3000',
   all(M * M * sigma(M + 1) <= 1 - mp.mpf(1) / (M + 1) for M in range(1, 3001)))

# ---------------------------------------------------------------- F1 - F6
N = 3000
av = [a(K) for K in range(0, N + 2)]
ok(f'F1: a(K) > 0, K = 0..{N}', all(av[K] > 0 for K in range(0, N + 1)))
ok(f'F2: a(K+1) < a(K), K = 0..{N}', all(av[K + 1] < av[K] for K in range(0, N + 1)))
ok(f'F3: a(K)+a(K+1) <= 1/(2(K+1)), K = 2..{N}',
   all(av[K] + av[K + 1] <= mp.mpf(1) / (2 * (K + 1)) for K in range(2, N + 1)))
ok('F3 fails at K = 1 (so K >= 2 is needed): a(1)+a(2) > 1/4', av[1] + av[2] > mp.mpf(1) / 4)
wv = {K: w(K) for K in range(0, 1201)}
ok('F4: w(K) > 0, K = 2..1200', all(wv[K] > 0 for K in range(2, 1201)))
ok('F4: (K+1)(a(K)+a(K+1)) <= 4 w(K), K = 2..1200',
   all((K + 1) * (av[K] + av[K + 1]) <= 4 * wv[K] for K in range(2, 1201)))
ok('F5: a(1) - 2/21 - a(3) > 0', av[1] - mp.mpf(2) / 21 - av[3] > 0)
ok('F5: a(1) - 2/21 + a(2) <= 2/7', av[1] - mp.mpf(2) / 21 + av[2] <= mp.mpf(2) / 7)
ok('F5: a(1) < 5/21', av[1] < mp.mpf(5) / 21)
ok('F6: a(1) < 1/4 and a(3) < 1/20', av[1] < mp.mpf(1) / 4 and av[3] < mp.mpf(1) / 20)
print('   F5 slacks:', mp.nstr(av[1] - mp.mpf(2) / 21 - av[3], 6), mp.nstr(mp.mpf(2) / 7 - (av[1] - mp.mpf(2) / 21 + av[2]), 6),
      mp.nstr(mp.mpf(5) / 21 - av[1], 6))
ok(f'Cor: a(K) < 1/(2(K+1)), K = 1..{N}', all(av[K] < mp.mpf(1) / (2 * (K + 1)) for K in range(1, N + 1)))
print('   a(K)(K+1)^2 at K = 10, 100, 1000, 3000:', [mp.nstr(av[K] * (K + 1)**2, 8) for K in (10, 100, 1000, 3000)])

# ---------------------------------------------------------------- omega identity
ok('omega(k) = (-1)^k (2k beta(k+1) - 1) + 2k beta(2k) - 1/2, k = 1..300',
   all(abs(omega(kk) - ((-1)**kk * (2 * kk * beta(kk + 1) - 1) + 2 * kk * beta(2 * kk) - mp.mpf(1) / 2))
       < mp.mpf(10)**-45 for kk in range(1, 301)))
# omega rational exactly
omF = lambda kk: sum((F((-1)**y * kk, y * (y - 1)) for y in range(kk + 1, 2 * kk + 1)), F(0))
print('   omega(2), omega(3), omega(4) =', omF(2), omF(3), omF(4), '; w(2), w(3) =', (-1)**2 * omF(3), (-1)**3 * omF(4))

# ---------------------------------------------------------------- exact enclosures via Lemma B
def uF(y):
    y = F(y)
    return 1 / (2 * y) + F(1, 4) / y**2 - F(1, 8) / y**4 + F(1, 4) / y**6


def epsF(y):
    y = F(y)
    return (17 * y**4 + 34 * y**3 + 29 * y**2 + 12 * y + 2) / (8 * y**6 * (y + 1)**6)


encl = {}
for KK, xx in ((1, 2), (2, 3), (3, 4)):
    lo = 4 * KK * KK * (uF(xx) - epsF(xx)) + 1 - 2 * KK
    hi = 4 * KK * KK * uF(xx) + 1 - 2 * KK
    encl[KK] = (lo, hi)
    print(f'   exact enclosure a({KK}) in [{float(lo):.8f}, {float(hi):.8f}]  (true {mp.nstr(av[KK], 10)})')
ok('Lean aF_one_bounds: 0.227 < a(1)-enclosure < 0.2344', encl[1][0] > F(227, 1000) and encl[1][1] < F(2344, 10000))
ok('Lean aF_two_bounds: 0.0901 < a(2)-enclosure < 0.092', encl[2][0] > F(901, 10000) and encl[2][1] < F(92, 1000))
ok('Lean aF_three_bounds: 0.0466 < a(3)-enclosure < 0.0472', encl[3][0] > F(466, 10000) and encl[3][1] < F(472, 10000))
# F5, F6 from the decimal bounds alone (as in the paper / Lean)
a1l, a1h, a2l, a2h, a3l, a3h = F(227, 1000), F(2344, 10000), F(901, 10000), F(92, 1000), F(466, 10000), F(472, 10000)
ok('F5 from decimals: a1l - 2/21 - a3h > 0', a1l - F(2, 21) - a3h > 0)
ok('F5 from decimals: a1h - 2/21 + a2h <= 2/7', a1h - F(2, 21) + a2h <= F(2, 7))
ok('F5 from decimals: a1h < 5/21', a1h < F(5, 21))
ok('F6 from decimals: a1h < 1/4, a3h < 1/20', a1h < F(1, 4) and a3h < F(1, 20))
print('   slacks from decimals:', float(a1l - F(2, 21) - a3h), float(F(2, 7) - (a1h - F(2, 21) + a2h)), float(F(5, 21) - a1h))

# ---------------------------------------------------------------- alpha*
def alpha_star(K, M):
    return (a(K) - (-1)**(K + M) * a(M)) / (2 * w(K))


allok = True
worst = mp.mpf(10)
for K in range(2, 151):
    for M in range(K + 1, K + 151):
        al = alpha_star(K, M)
        allok &= (0 < al <= mp.mpf(2) / (K + 1))
        worst = min(worst, (mp.mpf(2) / (K + 1) - al) * (K + 1))
ok('0 < alpha*(K,M) <= 2/(K+1) for 2<=K<=150, K+1<=M<=K+150', allok)
print('   min relative slack (2/(K+1) - alpha*)(K+1):', mp.nstr(worst, 8))
# alpha* kills the bulk parity amplitude: A = A_ren + 2 alpha omega(K+1) = 0
allok = True
for K in range(2, 60):
    for M in range(K + 1, K + 40):
        Aren = (-1)**(K + 1) * a(K) + (-1)**M * a(M)
        allok &= abs(Aren + 2 * alpha_star(K, M) * omega(K + 1)) < mp.mpf(10)**-45
ok('A_ren + 2 alpha* omega(K+1) = 0 (K < 60)', allok)

print()
if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)
print('ALL NUMERIC FACT CHECKS PASSED')
