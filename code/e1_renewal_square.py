"""E1: renewal (reversal-block flow) construction for squares [0,m] in box n >= m+2; exact check.
Blocks = intervals, each contributes its antidiagonal (reversal involution).
H(l) = 1 - K^2/((n-l)(n-l+1)), K = n-m-1, for 1<=l<=m+1; boundary blocks [0,l-1],[n-l,n-1] weight H(l);
interior blocks [a,a+l-1] (1<=a, a+l<=n-1) weight H(l)-H(l+1)."""
import sys
from fractions import Fraction as Fr
from common import profile, rowsum, check_exact, zero, add_antidiag


def H(n, m, l):
    if l < 1 or l > m + 1:
        return Fr(0)
    K = n - m - 1
    return 1 - Fr(K * K, (n - l) * (n - l + 1))


def sq_renewal(n, m):
    u = zero(n)
    if m == n - 1:
        return [[Fr(1)] * n for _ in range(n)]
    for l in range(1, m + 2):
        h = H(n, m, l)
        add_antidiag(u, 0, l, h)
        add_antidiag(u, n - l, l, h)
        al = h - H(n, m, l + 1)
        for a in range(1, n - l):
            add_antidiag(u, a, l, al)
    return u


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    bad = 0
    cnt = 0
    for n in range(1, N + 1):
        for m in range(0, n):
            u = sq_renewal(n, m)
            ok, msg = check_exact(u, n, 0, m)
            cnt += 1
            if not ok:
                bad += 1
                print("FAIL", n, m, msg)
    print(f"checked {cnt} (n<= {N}), failures {bad}")
