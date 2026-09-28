"""The all-n UNIF construction (P-PROOF).  For 0 <= lo <= hi <= n-1 returns the dipole amplitudes {level t: D_t}
(s-coordinates, level t = hi) used on top of the renewal difference D_ren = C_hi - C_{lo-1}:
  hi = n-1 or lo = 0 or 2*hi <= n-1 : no dipole (complement / renewal square / D_ren)
  K = n-1-hi = 1 (hi = n-2), 2*hi >= n : dipole at level hi, amplitude 2/7
  K >= 2, 2*hi >= n                   : dipole at level hi, amplitude alpha* = |A_ren| / (2 |omega(K+1)|),
      A_ren = (-1)^(K+1) a(K) + (-1)^M a(M), M = n - lo,  a(K) = 4K^2 beta(K+1) + 1 - 2K,
      omega(k) = sum_{y=k+1}^{2k} (-1)^y k / (y(y-1)),  beta(x) = sum_{j>=0} (-1)^j/(x+j).
alpha* is irrational; alpha_rat(n,lo,hi,den) returns a rational approximation (for exact sanity checks)."""
from fractions import Fraction as F
import mpmath as mp
mp.mp.dps = 80

def beta_mp(x):
    return (mp.digamma(mp.mpf(x + 1) / 2) - mp.digamma(mp.mpf(x) / 2)) / 2

def a_mp(K):
    return 4 * K * K * beta_mp(K + 1) + 1 - 2 * K

def omega(k):
    return sum(F((-1) ** y * k, y * (y - 1)) for y in range(k + 1, 2 * k + 1))

def alpha_star_mp(K, M):
    A = (-1) ** (K + 1) * a_mp(K) + (-1) ** M * a_mp(M)
    return -A / (2 * mp.mpf(omega(K + 1).numerator) / omega(K + 1).denominator)

def amplitudes(n, lo, hi, den=10 ** 40):
    if hi == n - 1 or lo == 0 or 2 * hi <= n - 1:
        return {}
    K = n - 1 - hi
    if K == 1:
        return {hi: F(2, 7)}
    al = alpha_star_mp(K, n - lo)
    return {hi: F(str(mp.nstr(al, 60, min_fixed=-mp.inf, max_fixed=mp.inf))).limit_denominator(den)}
