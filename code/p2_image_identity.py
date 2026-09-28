"""Phase 2 / P2k: EXACT check of the two-term (image) representation of renewal squares:
   U^m_c(i,j) = Psi(|i-j|+1) + Psi(m'(i,j)+1),   m' = min(i+j+1, 2c-1-i-j),
   Psi(p) = sum_{l>=p} (-1)^(l-p) H(l),  H(l) = 1 - K^2/((c-l)(c-l+1)) (1<=l<=m+1), 0 beyond, K = c-1-m.
Consequence: D_ren = U^hi_n - U^{lo-1}_n has cells C(s) + C(m') with C(p) = Psi_P(p+1) - Psi_N(p+1), so
   D_ren >= 0  <=>  C(p) >= 0 for all p in [0,n-1]   (1D condition).
Also report where C < 0 (the failure region of D_ren)."""
import sys
from fractions import Fraction as Fr
from p2_rays import Hfun
from e1_renewal_square import sq_renewal


def Psi_list(c, m):
    H = Hfun(c, m)
    Ps = [Fr(0)] * (c + 3)
    for p in range(c + 1, 0, -1):
        Ps[p] = H(p) - Ps[p + 1]
    return Ps


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    mism = 0; cnt = 0
    for c in range(1, N + 1):
        for m in range(c):
            if m == c - 1:
                continue
            Ps = Psi_list(c, m)
            U = sq_renewal(c, m)
            for i in range(c):
                for j in range(c):
                    s, S = abs(i - j), i + j
                    mp = min(S + 1, 2 * c - 1 - S)
                    cnt += 1
                    if U[i][j] != Ps[s + 1] + Ps[mp + 1]:
                        mism += 1
    print(f"two-term identity checked on {cnt} cells (c<={N}): mismatches {mism}")
