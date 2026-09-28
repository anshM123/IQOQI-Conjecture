"""Exact (Fractions) check of the P-PROOF construction with the coordinator's independent T/H/G builder
(unif/coord/coord_check_dip.build_THG): fast 1-D cell check for all intervals, full matrix check optional."""
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'unif', 'coord'))
from fractions import Fraction as F
from coord_check_dip import build_THG, U_matrix
from construct import amplitudes

def fast_ok(n, lo, hi, D):
    T, Hf, G, r = build_THG(n, lo, hi, D)
    Hv = [Hf(t) for t in range(n + 1)]
    mn = [None] * (n + 3); mx = [None] * (n + 3)
    for t in range(n - 1, 0, -1):
        pm, px = (mn[t + 2], mx[t + 2]) if t + 2 <= n - 1 else (None, None)
        mn[t] = Hv[t] if pm is None else min(Hv[t], pm)
        mx[t] = Hv[t] if px is None else max(Hv[t], px)
    for s in range(n):
        if s + 1 <= n - 1:
            if not (0 <= T[s] + mn[s + 1] and T[s] + mx[s + 1] <= 2): return ('cellH', s)
        if (n - s) % 2 == 1:
            g = G(s)
            if not (0 <= T[s] + g <= 2): return ('cellG', s)
    return True

def full_ok(n, lo, hi, D):
    U, r = U_matrix(n, lo, hi, D)
    R = F((hi + 1) ** 2 - lo * lo, n)
    for i in range(n):
        if sum(U[i]) != R: return 'row'
        for j in range(n):
            if U[i][j] != U[j][i]: return 'sym'
            if not (0 <= U[i][j] <= 1): return 'range'
    for s in range(n):
        if sum(U[i][i + s] for i in range(n - s)) != r[s]: return 'run'
    return True

if __name__ == '__main__':
    mode = sys.argv[1]; ns = [int(v) for v in sys.argv[2:]]
    for n in ns:
        t0 = time.time(); bad = []; ndip = 0
        for hi in range(n):
            for lo in range(hi + 1):
                D = amplitudes(n, lo, hi)
                ndip += bool(D)
                res = full_ok(n, lo, hi, D) if mode == 'full' else fast_ok(n, lo, hi, D)
                if res is not True: bad.append((lo, hi, res))
        print(f'n={n}: {mode} exact check of all {n*(n+1)//2} intervals ({ndip} with a dipole): failures {bad[:10]} ({time.time()-t0:.1f}s)', flush=True)
