"""INDEPENDENT implementation (from the P-HOOK2 Phase-3 report formulas only) of the per-interval
dipole construction for UNIF(n, lo, hi), with amplitudes read from hook2/certs/unif_dip_n{n}.txt:
  s = |i-j|, m' = min(i+j+1, 2n-1-i-j) (m' = n exactly on i+j = n-1);
  G(u) = sum_t D_t [u <= 2t-n-1];  T(s) = 0 for s > hi and, downward from s = hi,
  (n-s)T(s) + 2 sum_{t=s+1,s+3,..<=hi} T(t) = 2 r_s + 2 sum_{t dipole, t-s odd >0} D_t - [n-s odd] G(s);
  H = T - D;  U(i,j) = (T(s) + H(m'))/2 off the antidiagonal, (T(s) + G(s))/2 on it.
Mode 'full' (small n): builds every matrix and checks symmetry, 0<=U<=1, run sums r_s, rows ((hi+1)^2-lo^2)/n exactly;
also checks that with D = 0 the construction equals the renewal difference U^hi - U^{lo-1} (coord_check_X.renewal).
Mode 'fast': exact 1-D cell check via the level structure (each run s meets levels t = s+1 mod 2 in (s,n) and, iff n-s
odd, the antidiagonal G-cell), using parity-class suffix min/max of H."""
import sys, os, re
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coord_check_X import renewal

CERTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'certificates', 'per_interval_dipole')


def load_amps(n):
    amps = {}
    path = os.path.join(CERTS, f'unif_dip_n{n}.txt')
    if not os.path.exists(path):
        return None
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        lo, hi, t, v = line.split()
        amps.setdefault((int(lo), int(hi)), {})[int(t)] = F(v)
    return amps


def build_THG(n, lo, hi, D):
    r = [max(0, hi - max(lo, s) + 1) for s in range(n + 1)]   # = #{a in [lo,hi] : a >= s}
    def G(u):
        return sum((v for t, v in D.items() if u <= 2 * t - n - 1), F(0))
    T = [F(0)] * (n + 2)
    tail = [F(0), F(0)]          # running sums of T over t = s+1, s+3, ... (by parity of t)
    for s in range(hi, -1, -1):
        same_parity_above = tail[(s + 1) % 2]    # sum_{t = s+1, s+3, ... <= hi} T(t)
        rhs = 2 * r[s] + 2 * sum((v for t, v in D.items() if t > s and (t - s) % 2 == 1), F(0))
        if (n - s) % 2 == 1:
            rhs -= G(s)
        T[s] = (rhs - 2 * same_parity_above) / (n - s)
        tail[s % 2] += T[s]
    Hf = lambda t: T[t] - D.get(t, F(0)) if t <= n else F(0)
    return T, Hf, G, r


def U_matrix(n, lo, hi, D):
    T, Hf, G, r = build_THG(n, lo, hi, D)
    U = [[F(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = abs(i - j)
            if i + j == n - 1:
                U[i][j] = (T[s] + G(s)) / 2
            else:
                U[i][j] = (T[s] + Hf(min(i + j + 1, 2 * n - 1 - i - j))) / 2
    return U, r


def full_check(n, amps):
    R_ok = 0
    for hi in range(n):
        for lo in range(hi + 1):
            D = amps.get((lo, hi), {}) if amps else {}
            U, r = U_matrix(n, lo, hi, D)
            R = F((hi + 1) ** 2 - lo * lo, n)
            for i in range(n):
                assert sum(U[i]) == R, ('row', n, lo, hi, i)
                for j in range(n):
                    assert U[i][j] == U[j][i]
                    assert 0 <= U[i][j] <= 1, ('range', n, lo, hi, i, j, U[i][j])
            for s in range(n):
                assert sum(U[i][i + s] for i in range(n - s)) == r[s], ('run', n, lo, hi, s)
            if not D and hi <= n - 2:
                P, N = renewal(n, hi), renewal(n, lo - 1)
                assert all(U[i][j] == P[i][j] - N[i][j] for i in range(n) for j in range(n)), ('L7', n, lo, hi)
            R_ok += 1
    return R_ok


def fast_check(n, amps):
    cnt = 0
    for hi in range(n):
        for lo in range(hi + 1):
            D = amps.get((lo, hi), {}) if amps else {}
            T, Hf, G, r = build_THG(n, lo, hi, D)
            Hv = [Hf(t) for t in range(n + 1)]
            # suffix min/max of H over t in (s, n) with t = s+1 mod 2
            mn = [None] * (n + 2); mx = [None] * (n + 2)
            for t in range(n - 1, 0, -1):
                prev_mn, prev_mx = (mn[t + 2], mx[t + 2]) if t + 2 <= n - 1 else (None, None)
                mn[t] = Hv[t] if prev_mn is None else min(Hv[t], prev_mn)
                mx[t] = Hv[t] if prev_mx is None else max(Hv[t], prev_mx)
            for s in range(n):
                if s + 1 <= n - 1:
                    assert 0 <= T[s] + mn[s + 1] and T[s] + mx[s + 1] <= 2, ('cellH', n, lo, hi, s)
                if (n - s) % 2 == 1:
                    assert 0 <= T[s] + G(s) <= 2, ('cellG', n, lo, hi, s)
            cnt += 1
    return cnt


if __name__ == '__main__':
    mode, N1, N2 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    for n in range(N1, N2 + 1):
        amps = load_amps(n)
        if amps is None and n > 16:
            print(f'n={n}: no amplitude file (skipped)', flush=True); continue
        k = full_check(n, amps) if mode == 'full' else fast_check(n, amps)
        print(f'n={n}: {mode} check PASSED for all {k} intervals ({0 if not amps else len(amps)} corrected)', flush=True)
