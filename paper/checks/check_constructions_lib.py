"""Library: the interval uniformisations of main.tex (Sections 4-6), implemented from the paper's formulas.
Used by check_wk.py and check_end_to_end.py.  (check_constructions.py contains the same definitions inline.)

uniformisation(n, lo, hi)        -> n x n list of Fractions (alpha* rationalised to denominator <= 1e30)
uniformisation_float(n, lo, hi)  -> n x n list of floats (alpha* from mpmath)
"""
from fractions import Fraction as F
from functools import lru_cache
import mpmath as mp

mp.mp.dps = 50


def beta(x):
    x = mp.mpf(x)
    return (mp.digamma((x + 1) / 2) - mp.digamma(x / 2)) / 2


@lru_cache(maxsize=None)
def a(K):
    return 4 * K * K * beta(K + 1) + 1 - 2 * K


@lru_cache(maxsize=None)
def w(K):
    k = K + 1
    om = sum(mp.mpf((-1)**y * k) / (y * (y - 1)) for y in range(k + 1, 2 * k + 1))
    return (-1)**K * om


def alpha_star(K, M):
    return (a(K) - (-1)**(K + M) * a(M)) / (2 * w(K))


def renewal_closed(n, m, num=F):
    """U^m_n for 0 <= m <= n-2 (closed form)."""
    K = n - m - 1

    def H(l):
        if 1 <= l <= m + 1:
            return num(1) - num(K * K) / ((n - l) * (n - l + 1))
        return num(0)

    Hc = {l: H(l) for l in range(0, 2 * n + 4)}
    A = {p: sum(((-1)**t * Hc.get(p + t, num(0)) for t in range(m + 2)), num(0)) for p in range(0, 2 * n + 2)}
    return [[A[abs(i - j) + 1] + A[min(i + j + 2, 2 * n - i - j)] for j in range(n)] for i in range(n)]


def case_of(n, lo, hi):
    K = n - 1 - hi
    if n <= 2 * K + 1:
        return 'C'
    if K == 1:
        return 'D'
    return 'E'


def amplitude(n, lo, hi, num=F):
    c = case_of(n, lo, hi)
    if c == 'C':
        return num(0)
    if c == 'D':
        return num(2) / 7
    al = alpha_star(n - 1 - hi, n - lo)
    if num is F:
        return F(mp.nstr(al, 45, min_fixed=-mp.inf, max_fixed=mp.inf)).limit_denominator(10**30)
    return float(al)


def dipole_matrix(n, lo, hi, alpha, num=F):
    K, M = n - 1 - hi, n - lo

    def qL(L, x):
        return (2 * x * (x - 1) - 2 * L * L) if x >= L + 1 else 0

    def Q(x):
        return qL(K, x) - qL(M, x) + (2 * (K + 1) * alpha if K + 2 <= x <= 2 * K + 2 else 0)

    tau = [num(0), num(0)]
    for x in range(2, n + 1):
        tau.append(num(Q(x)) / (x * (x - 1)) - tau[x - 1])
    T = lambda s: tau[n - s] if s <= n else num(0)
    H = lambda u: T(u) - (alpha if u == hi else 0)
    G = lambda u: alpha if u + n + 1 <= 2 * hi else num(0)
    Y = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = abs(i - j)
            if i + j == n - 1:
                Y[i][j] = (T(s) + G(s)) / 2
            else:
                Y[i][j] = (T(s) + H(min(i + j + 1, 2 * n - 1 - i - j))) / 2
    return Y


def uniformisation(n, lo, hi, num=F):
    assert 0 <= lo <= hi <= n - 1
    if lo == 0 and hi == n - 1:
        return [[num(1)] * n for _ in range(n)]
    if hi == n - 1:
        U = renewal_closed(n, lo - 1, num)
        return [[num(1) - U[i][j] for j in range(n)] for i in range(n)]
    if lo == 0:
        return renewal_closed(n, hi, num)
    return dipole_matrix(n, lo, hi, amplitude(n, lo, hi, num), num)


def uniformisation_float(n, lo, hi):
    return uniformisation(n, lo, hi, num=float)
