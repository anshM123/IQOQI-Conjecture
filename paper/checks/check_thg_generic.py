"""Exact checks of the generic T/H/G lemmas of main.tex (Section "T/H/G matrices") with RANDOM rational T, H, G:

  L1 (levels)  for i, j < n, s = |i-j|, m' = min(i+j+1, 2n-1-i-j):  m' - s is odd and >= 1, m' <= n,
               m' = n  iff  i + j = n - 1,  and  n - s is odd if i + j = n - 1.
  L2 (runs)    R(s) = 0 (s >= n), R(n-1) = (T(n-1)+G(n-1))/2, R(n-2) = T(n-2) + H(n-1), and for s <= n-3
               2R(s) - 2R(s+2) = (n-s)T(s) - (n-s-2)T(s+2) + 2H(s+1) + [n-s odd](G(s) - G(s+2)).
  L3 (rows)    2 rho(r+1) - 2 rho(r) = [T(r+1)-H(r+1)] - [T(n-1-r)-H(n-1-r)] + G(|2r+3-n|) - G(|2r+1-n|).
  L4           mass count: a symmetric box matrix with run sums r_s of [lo,hi] and constant rows c has
               c = ((hi+1)^2 - lo^2)/n   (checked on the renewal squares and dipoles, which have constant rows).
  G-window     for 2 hi >= n:  [|2r+1-n| <= 2hi-n-1] = [n-hi <= r <= hi-1]  and the row increment of the
               dipole vanishes; and [y odd](G(s) - G(s+2)) = alpha [y = 2K+1] for y = n-s-2 (any hi).
"""
import os
import sys
import random
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_constructions_lib import uniformisation  # noqa: E402

FAILS = []


def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond:
        FAILS.append(name)


def thg(n, T, H, G):
    Y = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = abs(i - j)
            if i + j == n - 1:
                Y[i][j] = (T[s] + G[s]) / 2
            else:
                Y[i][j] = (T[s] + H[min(i + j + 1, 2 * n - 1 - i - j)]) / 2
    return Y


ok('L1 levels', all(
    ((min(i + j + 1, 2 * n - 1 - i - j) - abs(i - j)) % 2 == 1)
    and (min(i + j + 1, 2 * n - 1 - i - j) - abs(i - j) >= 1)
    and (min(i + j + 1, 2 * n - 1 - i - j) <= n)
    and ((min(i + j + 1, 2 * n - 1 - i - j) == n) == (i + j == n - 1))
    and ((i + j != n - 1) or ((n - abs(i - j)) % 2 == 1))
    for n in range(1, 41) for i in range(n) for j in range(n)))

rng = random.Random(3)
allR = allRow = True
for n in range(1, 16):
    for trial in range(20):
        T = [F(rng.randint(-20, 20), rng.randint(1, 9)) for _ in range(2 * n + 3)]
        H = [F(rng.randint(-20, 20), rng.randint(1, 9)) for _ in range(2 * n + 3)]
        G = [F(rng.randint(-20, 20), rng.randint(1, 9)) for _ in range(2 * n + 3)]
        Y = thg(n, T, H, G)
        R = lambda s: sum(Y[i][i + s] for i in range(n - s)) if s < n else F(0)
        if n >= 1:
            allR &= R(n - 1) == (T[n - 1] + G[n - 1]) / 2
        if n >= 2:
            allR &= R(n - 2) == T[n - 2] + H[n - 1]
        for s in range(0, n - 2):
            lhs = 2 * R(s) - 2 * R(s + 2)
            rhs = (n - s) * T[s] - (n - s - 2) * T[s + 2] + 2 * H[s + 1] + ((G[s] - G[s + 2]) if (n - s) % 2 == 1 else 0)
            allR &= lhs == rhs
        rho = [sum(Y[r]) for r in range(n)]
        for r in range(0, n - 1):
            lhs = 2 * rho[r + 1] - 2 * rho[r]
            rhs = (T[r + 1] - H[r + 1]) - (T[n - 1 - r] - H[n - 1 - r]) + G[abs(2 * r + 3 - n)] - G[abs(2 * r + 1 - n)]
            allRow &= lhs == rhs
ok('L2 run recurrence and top runs (random rational T,H,G, n <= 15)', allR)
ok('L3 row-shift identity (random rational T,H,G, n <= 15)', allRow)

# L4: constant-row value on all actual uniformisations (n <= 16)
allM = True
for n in range(1, 17):
    for hi in range(n):
        for lo in range(hi + 1):
            Y = uniformisation(n, lo, hi)
            rows = [sum(Y[r]) for r in range(n)]
            allM &= all(r == rows[0] for r in rows) and rows[0] == F((hi + 1)**2 - lo * lo, n)
            allM &= sum(sum(Y[i][i + s] for i in range(n - s)) + sum(Y[i + s][i] for i in range(n - s)) for s in range(1, n)) \
                + sum(Y[i][i] for i in range(n)) == (hi + 1)**2 - lo * lo
ok('L4 constant rows equal ((hi+1)^2-lo^2)/n; total mass = sum_{a in [lo,hi]}(2a+1) (all intervals, n <= 16)', allM)

# G-window identities
allG = True
for n in range(3, 60):
    for hi in range(1, n - 1):
        if 2 * hi >= n:
            for r in range(n):
                allG &= (abs(2 * r + 1 - n) <= 2 * hi - n - 1) == (n - hi <= r <= hi - 1)
            # row increment of the dipole: alpha([r+1 = hi] - [n-1-r = hi]) + G(|2r+3-n|) - G(|2r+1-n|) = 0
            for r in range(n - 1):
                Gf = lambda u: 1 if u + n + 1 <= 2 * hi else 0
                inc = (1 if r + 1 == hi else 0) - (1 if n - 1 - r == hi else 0) + Gf(abs(2 * r + 3 - n)) - Gf(abs(2 * r + 1 - n))
                allG &= inc == 0
        K = n - 1 - hi
        Gf = lambda u: 1 if u + n + 1 <= 2 * hi else 0
        for s in range(0, n - 2):
            y = n - s - 2
            allG &= ((Gf(s) - Gf(s + 2)) if y % 2 == 1 else 0) == (1 if y == 2 * K + 1 else 0)
ok('G-window identities (n < 60)', allG)

print()
if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)
print('ALL GENERIC T/H/G CHECKS PASSED')
