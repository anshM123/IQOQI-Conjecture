"""Independent full-matrix check of the Phase-3 UNIF construction for all intervals (small n): rebuild the n x n
matrix from (T,H,G) and check symmetry, 0<=u<=1, run sums #{a in [lo,hi]: a>=s}, rows ((hi+1)^2-lo^2)/n."""
import sys
from fractions import Fraction as F
from p3_exact import recur
def mp(n, x): return min(x + 1, 2 * n - 1 - x)
def load_amps(n):
    amps = {}
    with open(f'certs/unif_dip_n{n}.txt') as f:
        for line in f:
            if line.startswith('#') or not line.strip(): continue
            lo, hi, t, v = line.split(); amps.setdefault((int(lo), int(hi)), {})[int(t)] = F(v)
    return amps
def build(n, lo, hi, amps):
    r = lambda s: F(2 * max(0, hi - max(lo, s) + 1))
    def rhs(s):
        v = r(s)
        for t, a in amps.items():
            if t > s and (t - s) % 2 == 1: v += 2 * a
            if (n - s) % 2 == 1 and s <= 2 * t - n - 1: v -= a
        return v
    T = recur(n, hi, rhs)
    H = [T[s] - amps.get(s, F(0)) for s in range(n + 2)]
    G = {u: sum((a for t, a in amps.items() if u <= 2 * t - n - 1), F(0)) for u in range(n)}
    M = [[F(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = abs(i - j)
            M[i][j] = (T[s] + (G[s] if i + j == n - 1 else H[mp(n, i + j)])) / 2
    return M
def check(n, lo, hi, M):
    R = F((hi + 1) ** 2 - lo ** 2, n)
    for i in range(n):
        if sum(M[i]) != R: return 'row'
        for j in range(n):
            if M[i][j] != M[j][i]: return 'sym'
            if not (0 <= M[i][j] <= 1): return 'range'
    for s in range(n):
        if sum(M[i][i + s] for i in range(n - s)) != max(0, hi - max(lo, s) + 1): return 'run'
    return True
for n in [int(v) for v in sys.argv[1:]]:
    amps = load_amps(n); bad = []
    for hi in range(n):
        for lo in range(hi + 1):
            res = check(n, lo, hi, build(n, lo, hi, amps.get((lo, hi), {})))
            if res is not True: bad.append((lo, hi, res))
    print(f'n={n}: full-matrix exact check of all {n*(n+1)//2} intervals: failures {bad}', flush=True)
