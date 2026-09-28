"""EXACT verification of the HALF construction for UNIF(n, lo, hi), all 0 <= lo <= hi < n, n in [N0, N1].

Construction (b = hi+1, K = n-b, windows W_t = [t, t+hi], t = 0..K, uniform weights 1/(K+1)):
    X = theta*U^hi_n + (1-theta)*A_J - 1/2*U^{lo-1}_n - 1/2*A_V,     theta = 1 - lo^2/(2 b^2),
    U^m_c   = renewal square [0,m] in box c (reversal-block flow, e1_renewal_square.py; U^{c-1}_c = J),
    A_J     = avg_t J[W_t],   A_V = avg_t (U^{lo-1}_b placed on W_t)   (for lo = 0 the lo-terms are absent).
Renewal cell formula (i <= j, s = j-i, S = i+j, K' = c-1-m, H(l) = 1 - K'^2/((c-l)(c-l+1)) for 1<=l<=m+1,
alpha_l = H(l)-H(l+1) (l<=m), alpha_{m+1} = H(m+1)):
    U(i,j) = [S+1 <= m+1] H(S+1) + [2c-1-S <= m+1] H(2c-1-S) + sum_{l = s+1 (mod 2), s+1 <= l <= Lmax} alpha_l,
    Lmax = min(m+1, S-1, 2c-3-S).
All arithmetic exact: every quantity is scaled to a common integer denominator G per case.
Checks: 0 <= X <= 1 (all cells), every row sum = ((hi+1)^2-lo^2)/n, every run sum = #{a in [lo,hi]: a >= s}.
Symmetry holds by construction (cell values are functions of |i-j| and i+j, and A_J, A_V are symmetric).
The renewal cell formula is cross-checked against the explicit block construction for c <= CHECKC."""
import sys
from fractions import Fraction as Fr
from math import lcm

CHECKC = 16


class Ren:
    """renewal square [0,m] in box c, exact; integer-scaled cell values"""

    def __init__(self, c, m):
        self.c, self.m = c, m
        self.J = (m == c - 1)
        if self.J:
            self.den = 1
            return
        Kp = c - 1 - m
        H = [Fr(0)] * (c + 2)
        for l in range(1, m + 2):
            H[l] = 1 - Fr(Kp * Kp, (c - l) * (c - l + 1))
        al = [Fr(0)] * (c + 2)
        for l in range(1, m + 2):
            al[l] = H[l] - H[l + 1]
        den = 1
        for x in H + al:
            den = lcm(den, x.denominator)
        self.den = den
        self.Hi = [int(x * den) for x in H]
        # parity prefix sums: PS[x] = sum_{l <= x, l = x mod 2} alpha_l
        PS = [0] * (c + 3)
        ali = [int(x * den) for x in al]
        for x in range(1, c + 3):
            PS[x] = (PS[x - 2] if x >= 2 else 0) + (ali[x] if x < len(ali) else 0)
        self.PS = PS

    def cell(self, i, j):
        """integer value U(i,j)*den"""
        if self.J:
            return 1
        c, m = self.c, self.m
        if i > j:
            i, j = j, i
        s, S = j - i, i + j
        v = 0
        if S + 1 <= m + 1:
            v += self.Hi[S + 1]
        if 2 * c - 1 - S <= m + 1:
            v += self.Hi[2 * c - 1 - S]
        Lmax = min(m + 1, S - 1, 2 * c - 3 - S)
        lo_ = s + 1
        if Lmax >= lo_:
            # largest l <= Lmax with l = s+1 mod 2
            top = Lmax if (Lmax - lo_) % 2 == 0 else Lmax - 1
            v += self.PS[top] - (self.PS[lo_ - 2] if lo_ >= 2 else 0)
        return v


def crosscheck(cmax):
    from e1_renewal_square import sq_renewal
    for c in range(1, cmax + 1):
        for m in range(c):
            B = sq_renewal(c, m)
            Rr = Ren(c, m)
            for i in range(c):
                for j in range(c):
                    if Fr(Rr.cell(i, j), Rr.den) != B[i][j]:
                        raise AssertionError(("formula mismatch", c, m, i, j))
    return True


def verify_case(n, lo, hi, Ucache):
    b = hi + 1
    K = n - b
    T = K + 1
    Uh = Ucache[(n, hi)]
    if lo == 0:
        # X = U^hi_n (theta = 1)
        G = Uh.den
        X = [[Uh.cell(i, j) for j in range(n)] for i in range(n)]
    else:
        Ul = Ucache[(n, lo - 1)]
        V = Ucache[(b, lo - 1)]
        # diagonal prefix sums of V (integers scaled by V.den): Dg[s][x] = sum_{x'<x} V(x', x'+s)
        Dg = []
        for s in range(b):
            row = [0]
            acc = 0
            for x in range(b - s):
                acc += V.cell(x, x + s)
                row.append(acc)
            Dg.append(row)
        dU, dL, dV = Uh.den, Ul.den, V.den
        # G = 2 b^2 T dU dL dV
        G = 2 * b * b * T * dU * dL * dV
        cU = (2 * b * b - lo * lo) * T * dL * dV      # theta*U  : theta = (2b^2-lo^2)/(2b^2), U = Uint/dU
        cJ = lo * lo * dU * dL * dV                    # (1-theta)*A_J : lo^2/(2b^2) * cntJ/T
        cL = b * b * T * dU * dV                       # 1/2 U_L : U_L = ULint/dL
        cV = b * b * dU * dL                           # 1/2 A_V : sumVint/(T dV)
        X = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                t0 = max(0, j - hi)
                t1 = min(i, K)
                cnt = t1 - t0 + 1 if t1 >= t0 else 0
                val = cU * Uh.cell(i, j) - cL * Ul.cell(i, j)
                if cnt > 0:
                    s = j - i
                    # sum_{t=t0..t1} V(i-t, j-t): x = i-t runs from i-t1 to i-t0
                    sv = Dg[s][i - t0 + 1] - Dg[s][i - t1]
                    val += cJ * cnt - cV * sv
                X[i][j] = val
                X[j][i] = val
    # checks
    R = Fr((hi + 1) ** 2 - lo ** 2, n)
    RG = R * G
    if RG.denominator != 1:
        return False, "R*G not integer"
    RG = int(RG)
    for i in range(n):
        for j in range(i, n):
            if X[i][j] < 0 or X[i][j] > G:
                return False, f"range ({i},{j}) {Fr(X[i][j], G)}"
    for i in range(n):
        if sum(X[i]) != RG:
            return False, f"row {i}"
    for s in range(n):
        rs = max(0, hi - max(lo, s) + 1)
        if sum(X[i][i + s] for i in range(n - s)) != rs * G:
            return False, f"run {s}"
    return True, "ok"


if __name__ == "__main__":
    N0, N1 = int(sys.argv[1]), int(sys.argv[2])
    if N0 <= 2:
        crosscheck(CHECKC)
        print(f"renewal cell formula cross-checked against block construction for all c <= {CHECKC}", flush=True)
    import time
    t0 = time.time()
    total = 0
    for n in range(N0, N1 + 1):
        Ucache = {}
        for c in range(1, n + 1):
            for m in range(c):
                if c == n or True:
                    pass
        # needed: (n, m) all m; (b, lo-1) for b <= n
        for m in range(n):
            Ucache[(n, m)] = Ren(n, m)
        for b in range(1, n):
            for m in range(b):
                Ucache[(b, m)] = Ren(b, m)
        fails = 0
        cnt = 0
        for hi in range(n):
            for lo in range(hi + 1):
                ok, msg = verify_case(n, lo, hi, Ucache)
                cnt += 1
                if not ok:
                    fails += 1
                    print("FAIL", n, lo, hi, msg, flush=True)
        total += cnt
        print(f"n={n}: {cnt} cases, failures {fails}  (elapsed {time.time()-t0:.0f}s)", flush=True)
    print(f"TOTAL {total} cases verified exactly, n in [{N0},{N1}]")
