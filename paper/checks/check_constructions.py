"""Independent re-implementation, FROM THE FORMULAS OF main.tex ONLY, of all interval uniformisations, and
exact / high-precision verification.  (A third implementation, next to the Lean definitions and the public
checkers in publish/IQOQI-Conjecture/code, which are only imported for cross-comparison.)

Paper definitions implemented here:
  renewal square  U^m_n(i,j) = A(|i-j|+1) + A(min(i+j+2, 2n-i-j)),  A(p) = sum_{t=0}^{m+1} (-1)^t H(p+t),
                  H(l) = 1 - K^2/((n-l)(n-l+1)) on 1 <= l <= m+1 (0 otherwise), K = n-m-1   (0 <= m <= n-2)
  J, complement J - U^{lo-1}_n
  one-dipole construction: K = n-1-hi, M = n-lo,
      q_L(x) = [x >= L+1](2x(x-1) - 2L^2),  Q(x) = q_K(x) - q_M(x) + 2(K+1) alpha [K+2 <= x <= 2K+2],
      tau(0) = tau(1) = 0, tau(x) = Q(x)/(x(x-1)) - tau(x-1)  (x >= 2),
      T(s) = tau(n-s), H(u) = T(u) - alpha [u = hi], G(u) = alpha [u + n + 1 <= 2 hi],
      Y(i,j) = (T(|i-j|) + H(min(i+j+1, 2n-1-i-j)))/2  (i+j != n-1),   (T(|i-j|) + G(|i-j|))/2 (i+j = n-1)
  amplitudes: case (C) n <= 2K+1: alpha = 0;  (D) K = 1, n >= 4: alpha = 2/7;
              (E) K >= 2, n >= 2K+2: alpha* = (a(K) - (-1)^(K+M) a(M)) / (2 w(K)).
Checks:
  R1  renewal closed form == block-reversal construction (public code in code/) for n <= 24, all m.
  R2  renewal: symmetric, entries in [0,1], band, runs m+1-s, rows (m+1)^2/n  (exact, n <= 30).
  R3  min(i+j+2, 2n-i-j) = |i-j| + 2 + 2 min(i, j, n-1-i, n-1-j)  (n <= 40).
  D1  dipole T equals the public (RUN)-recursion builder build_THG (exact, n <= 30, all intervals, same alpha).
  D2  exact full-matrix check of ALL intervals of ALL boxes n <= 22 (symmetry, [0,1], runs, rows); runs and
      rows are also checked for random rational alpha (they hold for ANY alpha when 2hi >= n or alpha = 0).
  D3  mpmath (50 digits, exact irrational alpha*) 1-D cell conditions (CELL1), (CELL2) for all intervals n <= 48.
  D4  closed form tau = Phi + s (case formulas of Section 8) in mpmath, all intervals n <= 40.
  D5  alpha = 0 construction equals the renewal difference U^hi - U^{lo-1} (remark), n <= 20.
  D6  case (D) values tau(1) = 0, tau(2) = 1, tau(3) in {4/21, 6/7}; case (C) (3,1,1): T = (0,1,0).
  D7  float64 1-D cell check of all intervals with K <= 6 for n <= 400 and random intervals for n in {600, 1001, 2000}.
"""
import os
import sys
import random
from fractions import Fraction as F
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
PUB = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..', 'publish', 'IQOQI-Conjecture', 'code'))
sys.dont_write_bytecode = True      # never write __pycache__ into the public package (read-only use)
sys.path.insert(0, PUB)
from coord_check_X import renewal as coord_renewal          # noqa: E402  (block-reversal definition)
from coord_check_dip import build_THG as coord_build_THG    # noqa: E402  ((RUN)-recursion definition)

mp.mp.dps = 50
FAILS = []


def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond:
        FAILS.append(name)


# ------------------------------------------------------------------------------------------ renewal
def renewal_closed(n, m):
    K = n - m - 1

    def H(l):
        return F(1) - F(K * K, (n - l) * (n - l + 1)) if 1 <= l <= m + 1 else F(0)

    Hc = {l: H(l) for l in range(0, 2 * n + 4)}
    A = {p: sum(((-1)**t * Hc.get(p + t, F(0)) for t in range(m + 2)), F(0)) for p in range(0, 2 * n + 2)}
    return [[A[abs(i - j) + 1] + A[min(i + j + 2, 2 * n - i - j)] for j in range(n)] for i in range(n)]


def J(n):
    return [[F(1)] * n for _ in range(n)]


def runs_rows(Y, n):
    runs = [sum(Y[i][i + s] for i in range(n - s)) for s in range(n)]
    rows = [sum(Y[i]) for i in range(n)]
    return runs, rows


def rvec(n, lo, hi):
    return [max(0, hi + 1 - max(lo, s)) for s in range(n)]


def is_unif(Y, n, lo, hi):
    for i in range(n):
        for j in range(n):
            if Y[i][j] != Y[j][i]:
                return 'sym'
            if not (0 <= Y[i][j] <= 1):
                return ('range', i, j, Y[i][j])
    runs, rows = runs_rows(Y, n)
    if runs != rvec(n, lo, hi):
        return 'runs'
    R = F((hi + 1)**2 - lo * lo, n)
    if any(r != R for r in rows):
        return 'rows'
    return True


allok = True
for n in range(2, 25):
    for m in range(0, n - 1):
        C = renewal_closed(n, m)
        B = coord_renewal(n, m)
        allok &= all(C[i][j] == B[i][j] for i in range(n) for j in range(n))
ok('R1 renewal closed form == block-reversal construction (n <= 24, all m <= n-2)', allok)

allok = True
for n in range(2, 31):
    for m in range(0, n - 1):
        U = renewal_closed(n, m)
        allok &= (is_unif(U, n, 0, m) is True)
        allok &= all(U[i][j] == 0 for i in range(n) for j in range(n) if abs(i - j) > m)
        # cell bound U(i,j) <= H(|i-j|+1)
        K = n - m - 1
        allok &= all(U[i][j] <= (F(1) - F(K * K, (n - abs(i - j) - 1) * (n - abs(i - j))) if abs(i - j) + 1 <= m + 1 else 0)
                     for i in range(n) for j in range(n))
    allok &= (is_unif(J(n), n, 0, n - 1) is True)
    for lo in range(1, n):
        U = renewal_closed(n, lo - 1)
        Cm = [[1 - U[i][j] for j in range(n)] for i in range(n)]
        allok &= (is_unif(Cm, n, lo, n - 1) is True)
ok('R2 renewal squares, J and complements are interval uniformisations (exact, n <= 30)', allok)

ok('R3 min(i+j+2, 2n-i-j) = |i-j| + 2 + 2 min(i, j, n-1-i, n-1-j)  (n <= 40)',
   all(min(i + j + 2, 2 * n - i - j) == abs(i - j) + 2 + 2 * min(i, j, n - 1 - i, n - 1 - j)
       for n in range(1, 41) for i in range(n) for j in range(n)))


# ------------------------------------------------------------------------------------------ special functions
def beta(x):
    x = mp.mpf(x)
    return (mp.digamma((x + 1) / 2) - mp.digamma(x / 2)) / 2


_a = {}


def a(K):
    if K not in _a:
        _a[K] = 4 * K * K * beta(K + 1) + 1 - 2 * K
    return _a[K]


_w = {}


def w(K):
    if K not in _w:
        k = K + 1
        om = sum(mp.mpf((-1)**y * k) / (y * (y - 1)) for y in range(k + 1, 2 * k + 1))
        _w[K] = (-1)**K * om
    return _w[K]


def sigma(x):
    return 4 * beta(x) - mp.mpf(2) / x


def alpha_star(K, M):
    return (a(K) - (-1)**(K + M) * a(M)) / (2 * w(K))


def case_of(n, lo, hi):
    K = n - 1 - hi
    if n <= 2 * K + 1:
        return 'C'
    if K == 1:
        return 'D'
    return 'E'


def amplitude(n, lo, hi, exact=False):
    c = case_of(n, lo, hi)
    if c == 'C':
        return F(0) if not exact else mp.mpf(0)
    if c == 'D':
        return F(2, 7) if not exact else mp.mpf(2) / 7
    K, M = n - 1 - hi, n - lo
    al = alpha_star(K, M)
    if exact:
        return al
    return F(mp.nstr(al, 45, min_fixed=-mp.inf, max_fixed=mp.inf)).limit_denominator(10**30)


# ------------------------------------------------------------------------------------------ dipole construction
def tau_seq(n, lo, hi, alpha, num=F):
    K, M = n - 1 - hi, n - lo

    def qL(L, x):
        return (2 * x * (x - 1) - 2 * L * L) if x >= L + 1 else 0

    def Q(x):
        return qL(K, x) - qL(M, x) + (2 * (K + 1) * alpha if K + 2 <= x <= 2 * K + 2 else 0)

    tau = [num(0), num(0)]
    for x in range(2, n + 1):
        tau.append(num(Q(x)) / (x * (x - 1)) - tau[x - 1] if num is F else
                   mp.mpf(Q(x)) / (x * (x - 1)) - tau[x - 1])
    return tau


def dipole_matrix(n, lo, hi, alpha):
    tau = tau_seq(n, lo, hi, alpha)
    T = lambda s: tau[n - s] if s <= n else F(0)
    H = lambda u: T(u) - (alpha if u == hi else 0)
    G = lambda u: alpha if u + n + 1 <= 2 * hi else F(0)
    Y = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = abs(i - j)
            if i + j == n - 1:
                Y[i][j] = (T(s) + G(s)) / 2
            else:
                Y[i][j] = (T(s) + H(min(i + j + 1, 2 * n - 1 - i - j))) / 2
    return Y, [T(s) for s in range(n)]


# D1: T equals the public (RUN)-recursion builder
allok = True
for n in range(3, 31):
    for hi in range(1, n - 1):
        for lo in range(1, hi + 1):
            al = amplitude(n, lo, hi)
            D = {} if al == 0 else {hi: al}
            Tc, Hf, G, r = coord_build_THG(n, lo, hi, D)
            _, T = dipole_matrix(n, lo, hi, al)
            allok &= all(T[s] == Tc[s] for s in range(n))
ok('D1 T(s) = tau(n-s) equals the (RUN)-recursion T of the public checker (exact, n <= 30, all 1<=lo<=hi<=n-2)', allok)

# D2: exact full-matrix check of all intervals n <= 22 (all four constructions)
allok = True
cnt = {'A': 0, 'B': 0, 'C': 0, 'D': 0, 'E': 0}
for n in range(1, 23):
    for hi in range(0, n):
        for lo in range(0, hi + 1):
            if lo == 0 and hi == n - 1:
                Y, c = J(n), 'A'
            elif hi == n - 1:
                U = renewal_closed(n, lo - 1)
                Y, c = [[1 - U[i][j] for j in range(n)] for i in range(n)], 'A'
            elif lo == 0:
                Y, c = renewal_closed(n, hi), 'B'
            else:
                c = case_of(n, lo, hi)
                Y, _ = dipole_matrix(n, lo, hi, amplitude(n, lo, hi))
            cnt[c] += 1
            res = is_unif(Y, n, lo, hi)
            if res is not True:
                print('   failure', n, lo, hi, c, res)
                allok = False
ok(f'D2 exact full-matrix check, ALL intervals of all boxes n <= 22 (counts {cnt})', allok)

# runs and rows hold for ANY alpha when alpha = 0 or 2 hi >= n
random.seed(1)
allok = True
for n in range(3, 19):
    for hi in range(1, n - 1):
        for lo in range(1, hi + 1):
            if 2 * hi < n:
                continue
            al = F(random.randint(-50, 50), random.randint(1, 40))
            Y, _ = dipole_matrix(n, lo, hi, al)
            runs, rows = runs_rows(Y, n)
            allok &= (runs == rvec(n, lo, hi)) and all(rr == F((hi + 1)**2 - lo * lo, n) for rr in rows)
            allok &= all(Y[i][j] == Y[j][i] for i in range(n) for j in range(n))
ok('D2b runs and rows hold for random rational alpha whenever 2hi >= n (exact, n <= 18)', allok)
# and rows FAIL in general for alpha != 0 when 2 hi < n (negative control)
bad = 0
for n in range(5, 15):
    for hi in range(1, n - 1):
        for lo in range(1, hi + 1):
            if 2 * hi >= n:
                continue
            Y, _ = dipole_matrix(n, lo, hi, F(1, 3))
            _, rows = runs_rows(Y, n)
            bad += any(rr != rows[0] for rr in rows)
ok(f'D2c negative control: alpha = 1/3 with 2hi < n breaks constant rows in {bad} cases (expected > 0)', bad > 0)


# D3: mpmath 1-D cell conditions with the exact (irrational) alpha*
def cells_ok_1d(n, lo, hi, alpha, tau):
    K = n - 1 - hi
    eta = [tau[y] - (alpha if y == K + 1 else 0) for y in range(n + 1)]
    mins = {0: None, 1: None}
    maxs = {0: None, 1: None}
    worst_lo, worst_hi = mp.mpf(10), mp.mpf(10)
    for x in range(1, n + 1):
        # pairs (x, y) with y < x, x - y odd: y has parity (x+1) % 2; prefix over y <= x-1
        par = (x + 1) % 2
        if mins[par] is not None:
            lo_v = tau[x] + mins[par]
            hi_v = tau[x] + maxs[par]
            worst_lo = min(worst_lo, lo_v)
            worst_hi = min(worst_hi, 2 - hi_v)
            if lo_v < 0 or hi_v > 2:
                return False, worst_lo, worst_hi
        # now add y = x to its class
        pc = x % 2
        mins[pc] = eta[x] if mins[pc] is None else min(mins[pc], eta[x])
        maxs[pc] = eta[x] if maxs[pc] is None else max(maxs[pc], eta[x])
        if x % 2 == 1:
            g = alpha if x >= 2 * K + 3 else 0
            v = tau[x] + g
            worst_lo = min(worst_lo, v)
            worst_hi = min(worst_hi, 2 - v)
            if v < 0 or v > 2:
                return False, worst_lo, worst_hi
    return True, worst_lo, worst_hi


allok = True
nint = 0
for n in range(3, 49):
    for hi in range(1, n - 1):
        for lo in range(1, hi + 1):
            al = amplitude(n, lo, hi, exact=True)
            tau = tau_seq(n, lo, hi, al, num=mp.mpf)
            good, wl, wh = cells_ok_1d(n, lo, hi, al, tau)
            nint += 1
            if not good:
                print('   1-D cell failure', n, lo, hi)
                allok = False
ok(f'D3 (CELL1),(CELL2) with exact alpha (mpmath 50 digits), all {nint} intervals 1<=lo<=hi<=n-2, n <= 48', allok)


# D4: closed form tau = Phi + s
def s_closed(n, lo, hi, x):
    K, M = n - 1 - hi, n - lo
    c = case_of(n, lo, hi)
    if c == 'C':
        return (-1)**(x + K + 1) * a(K) + ((-1)**(x + M) * a(M) if x >= M + 1 else 0)
    if c == 'D':
        return (-1)**x * (a(1) - mp.mpf(2) / 21 + ((-1)**M * a(M) if x >= M + 1 else 0))
    al = alpha_star(K, M)
    b = lambda y: (2 * (K + 1) * al / (y * (y - 1))) if K + 2 <= y <= 2 * K + 2 else 0
    tail = sum((-1)**j * b(x + 1 + j) for j in range(0, max(0, 2 * K + 2 - x)))
    return tail - ((-1)**(x + M) * a(M) if x <= M else 0)


allok = True
for n in range(3, 41):
    for hi in range(1, n - 1):
        for lo in range(1, hi + 1):
            K, M = n - 1 - hi, n - lo
            al = amplitude(n, lo, hi, exact=True)
            tau = tau_seq(n, lo, hi, al, num=mp.mpf)
            xmin = 4 if case_of(n, lo, hi) == 'D' else K + 1
            for x in range(xmin, n + 1):
                Phi = 1 - K * K * sigma(x) if x <= M else (M * M - K * K) * sigma(x)
                if abs(tau[x] - (Phi + s_closed(n, lo, hi, x))) > mp.mpf(10)**-35:
                    allok = False
            allok &= all(tau[x] == 0 for x in range(0, K + 1))
ok('D4 closed forms tau = Phi + s of cases (C), (D) [x>=4], (E), and tau = 0 on x <= K (n <= 40)', allok)

# D5: alpha = 0 construction == renewal difference
allok = True
for n in range(3, 21):
    for hi in range(1, n - 1):
        for lo in range(1, hi + 1):
            Y, _ = dipole_matrix(n, lo, hi, F(0))
            P, Nn = renewal_closed(n, hi), renewal_closed(n, lo - 1)
            allok &= all(Y[i][j] == P[i][j] - Nn[i][j] for i in range(n) for j in range(n))
ok('D5 the alpha = 0 T/H/G matrix equals U^hi_n - U^{lo-1}_n (n <= 20)', allok)

# D6: small values
allok = True
for n in range(4, 30):
    hi = n - 2
    for lo in range(1, hi + 1):
        M = n - lo
        tau = tau_seq(n, lo, hi, F(2, 7))
        allok &= tau[1] == 0 and tau[2] == 1 and tau[3] == (F(4, 21) if M == 2 else F(6, 7))
ok('D6 case (D): tau(1) = 0, tau(2) = 1, tau(3) = 4/21 (M = 2) or 6/7 (M >= 3)', allok)
Y, T = dipole_matrix(3, 1, 1, F(0))
# by hand: tau = (0,0,1,0), T = (T(0),T(1),T(2)) = (0,1,0), H = T, G = 0;
# Y(0,0) = (T(0)+H(1))/2 = 1/2, Y(0,1) = (T(1)+H(2))/2 = 1/2, Y(0,2) = Y(1,1) = 0 (antidiagonal), etc.
ok('D6 case (C), (n,lo,hi) = (3,1,1): T = (0, 1, 0), Y = [[1/2,1/2,0],[1/2,0,1/2],[0,1/2,1/2]]',
   T == [0, 1, 0] and Y == [[F(1, 2), F(1, 2), 0], [F(1, 2), 0, F(1, 2)], [0, F(1, 2), F(1, 2)]])

# D7: float64 checks for large n (near-top intervals K <= 6 exhaustively, random others)
def float_check(n, lo, hi):
    al = float(amplitude(n, lo, hi, exact=True))
    K, M = n - 1 - hi, n - lo
    tau = [0.0, 0.0]
    for x in range(2, n + 1):
        qK = (2 * x * (x - 1) - 2 * K * K) if x >= K + 1 else 0
        qM = (2 * x * (x - 1) - 2 * M * M) if x >= M + 1 else 0
        Q = qK - qM + (2 * (K + 1) * al if K + 2 <= x <= 2 * K + 2 else 0)
        tau.append(Q / (x * (x - 1)) - tau[x - 1])
    eta = [tau[y] - (al if y == K + 1 else 0) for y in range(n + 1)]
    mn = {0: None, 1: None}
    mx = {0: None, 1: None}
    low, up = 10.0, 10.0          # min cell sum (must be >= 0; exact zeros occur), min upper slack 2 - sum
    for x in range(1, n + 1):
        par = (x + 1) % 2
        if mn[par] is not None:
            low = min(low, tau[x] + mn[par])
            up = min(up, 2 - tau[x] - mx[par])
        pc = x % 2
        mn[pc] = eta[x] if mn[pc] is None else min(mn[pc], eta[x])
        mx[pc] = eta[x] if mx[pc] is None else max(mx[pc], eta[x])
        if x % 2 == 1:
            v = tau[x] + (al if x >= 2 * K + 3 else 0)
            low = min(low, v)
            up = min(up, 2 - v)
    return low, up


allok = True
minup = 10.0
for n in range(8, 401):
    for K in range(1, 7):
        hi = n - 1 - K
        for lo in range(1, hi + 1):
            low, up = float_check(n, lo, hi)
            minup = min(minup, up)
            if low < -1e-12 or up < -1e-12:
                allok = False
                print('   float failure', n, lo, hi, low, up)
ok(f'D7a float64 1-D cells, all intervals with K = n-1-hi <= 6, n <= 400 (min upper slack {minup:.3e})', allok)
random.seed(7)
allok = True
for n in (600, 1001, 2000):
    for _ in range(300):
        hi = random.randint(1, n - 2)
        lo = random.randint(1, hi)
        low, up = float_check(n, lo, hi)
        allok &= low > -1e-12 and up > -1e-12
ok('D7b float64 1-D cells, 300 random intervals each for n = 600, 1001, 2000', allok)

print()
if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)
print('ALL CONSTRUCTION CHECKS PASSED')
