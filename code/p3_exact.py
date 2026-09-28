"""EXACT UNIF(n,lo,hi) for all intervals via  U = D_ren(lo,hi) [+ alpha*dip(hi) + beta*dip(hi-1) if needed].
D_ren = cumulative image kernels C_hi - C_{lo-1} (T = H = C, G = 0); dipole at level t (> (n-1)/2, <= hi):
RHS change 2[t>s, t-s odd] - [n-s odd, s <= 2t-n-1], H = T - e_t, G = [u <= 2t-n-1].
Cells: 1/2(T(s)+H(m')) off the main antidiagonal (m' = min(i+j+1, 2n-1-i-j)), 1/2(T(s)+G(s)) on it.
Checks EXACTLY (Fractions) 0 <= cell <= 1 via parity-class suffix min/max of H (O(n) per interval).
Writes the dipole amplitudes to certs/unif_dip_n{n}.txt."""
import sys, time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

def recur(n, top, rhs):
    """T(s) for s = top..0 solving (n-s)T(s) + 2 sum_{t=s+1,s+3..<=top} T(t) = rhs(s)."""
    T = [F(0)] * (n + 2)
    par = [F(0), F(0)]   # running sums of T over t > s by parity of t
    for s in range(top, -1, -1):
        acc = par[(s + 1) % 2]
        T[s] = (rhs(s) - 2 * acc) / (n - s)
        par[s % 2] += T[s]
    return T

def cells_ok(n, T, H, G):
    """exact: 0 <= 1/2(T(s)+H(m')) <= 1 for every cell off the antidiagonal, and 1/2(T(s)+G(s)) on it."""
    # for run s: m' ranges over {s+1, s+3, ..., <= n-1} (each value occurs), plus level n (antidiagonal) iff n-s odd
    # suffix min/max of H over parity classes
    INF = None
    smin = {}; smax = {}
    mn = [None, None]; mx = [None, None]
    for t in range(n - 1, 0, -1):
        p = t % 2
        mn[p] = H[t] if mn[p] is None or H[t] < mn[p] else mn[p]
        mx[p] = H[t] if mx[p] is None or H[t] > mx[p] else mx[p]
        smin[t] = mn[p]; smax[t] = mx[p]
    for s in range(n):
        if s + 1 <= n - 1:
            lo_ = smin[s + 1]; hi_ = smax[s + 1]
            if T[s] + lo_ < 0 or T[s] + hi_ > 2: return False
        if (n - s) % 2 == 1:
            g = G.get(s, F(0))
            if T[s] + g < 0 or T[s] + g > 2: return False
    return True

def run(n, verbose=True):
    t0 = time.time()
    C = {-1: [F(0)] * (n + 2)}
    for m in range(n):
        C[m] = recur(n, m, lambda s, m=m: F(2 * (m - s + 1)))
    W = {}   # (hi, t) -> response T
    out = []; nfix = 0; nint = 0
    for hi in range(n):
        for lo in range(hi + 1):
            nint += 1
            T = [C[hi][s] - C[lo - 1][s] for s in range(n + 2)]
            H = list(T); G = {}
            if cells_ok(n, T, H, G): continue
            levels = [t for t in (hi, hi - 1) if 2 * t > n - 1 and t <= hi]
            if not levels: return f'n={n}: [{lo},{hi}] invalid and no dipole level'
            resp = {}
            for t in levels:
                if (hi, t) not in W:
                    W[(hi, t)] = recur(n, hi, lambda s, t=t: F(2 if (t > s and (t - s) % 2 == 1) else 0) - F(1 if ((n - s) % 2 == 1 and s <= 2 * t - n - 1) else 0))
                resp[t] = W[(hi, t)]
            # float LP: maximise min slack
            def cellrows(Tv, Hv, Gv):
                rows = []
                for s in range(n):
                    for mq in range(s + 1, n, 2):
                        rows.append((s, mq))
                return rows
            pairs = [(s, mq) for s in range(n) for mq in range(s + 1, n, 2)]
            ad = [s for s in range(n) if (n - s) % 2 == 1]
            k = len(levels)
            A_rows, b_rows = [], []
            def lin(s, mq=None):
                c0 = float(T[s]) + (float(H[mq]) if mq is not None else 0.0)
                cs = []
                for t in levels:
                    v = float(resp[t][s]) + ((float(resp[t][mq]) - (1.0 if mq == t else 0.0)) if mq is not None else (1.0 if s <= 2 * t - n - 1 else 0.0))
                    cs.append(v)
                return c0, cs
            def addrow(c0, cs):
                if max(abs(x) for x in cs) < 1e-14: return      # structurally constant cell (checked exactly later)
                nrm = max(abs(x) for x in cs)
                A_rows.append([-x for x in cs] + [nrm]); b_rows.append(c0)          # c0 + cs.x >= tau*nrm
                A_rows.append(cs + [nrm]); b_rows.append(2 - c0)                   # c0 + cs.x <= 2 - tau*nrm
            for (s, mq) in pairs:
                addrow(*lin(s, mq))
            for s in ad:
                addrow(*lin(s))
            res = linprog([0.0] * k + [-1.0], A_ub=np.array(A_rows), b_ub=np.array(b_rows),
                          bounds=[(-5, 5)] * k + [(None, 1.0)], method='highs')
            if res.status != 0 or res.x[-1] <= 0:
                return f'n={n}: [{lo},{hi}] two top dipoles INFEASIBLE (float), tau={res.x[-1] if res.status == 0 else None}'
            amps = {}
            for den in (10**3, 10**4, 10**5, 10**6, 10**8):
                amps = {t: F(res.x[i]).limit_denominator(den) for i, t in enumerate(levels)}
                T2 = [T[s] + sum(amps[t] * resp[t][s] for t in levels) for s in range(n + 2)]
                H2 = [T2[s] - sum(amps[t] for t in levels if t == s) for s in range(n + 2)]
                G2 = {u: sum(amps[t] for t in levels if u <= 2 * t - n - 1) for u in range((n - 1) % 2, n, 2)}
                if cells_ok(n, T2, H2, G2): break
            else:
                return f'n={n}: [{lo},{hi}] rational rounding failed'
            nfix += 1
            out.append((lo, hi, amps))
    with open(f'certs/unif_dip_n{n}.txt', 'w') as f:
        f.write(f'# UNIF(n={n},lo,hi): D_ren + dipoles; lines "lo hi level amplitude" for the corrected intervals\n')
        for lo, hi, amps in out:
            for t, v in amps.items(): f.write(f'{lo} {hi} {t} {v}\n')
    return f'n={n}: all {nint} intervals VALID (exact); {nfix} needed dipoles ({time.time()-t0:.1f}s)'

if __name__ == '__main__':
    for n in [int(v) for v in sys.argv[1:]]:
        print(run(n), flush=True)
