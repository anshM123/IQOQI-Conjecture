"""INDEPENDENT implementation (from the formulas in the P-UNIF report only; no P-UNIF code imported)
of the explicit uniformisation X(n, lo, hi) and exact check of UNIF(n, lo, hi):
  symmetric, 0 <= X <= 1, run sums r_s = #{a in [lo,hi]: a >= s}, row sums ((hi+1)^2 - lo^2)/n.
Renewal square U^m_n (0 <= m <= n-2): K = n-m-1, H(l) = 1 - K^2/((n-l)(n-l+1)) for 1<=l<=m+1, H(l) = 0 for l > m+1;
  end blocks [0,l-1], [n-l,n-1] weight H(l); interior blocks [a,a+l-1] (1<=a<=n-1-l) weight H(l)-H(l+1);
  each block contributes weight * reversal permutation of the block.  U^{n-1}_n = J, U^{-1}_n = 0.
X = th*U^hi_n + (1-th)*avg_t J[W_t] - 1/2 U^{lo-1}_n - 1/2 avg_t U^{lo-1}_b[W_t],  b = hi+1, W_t = [t, t+hi], t=0..n-b,
  th = 1 - lo^2/(2 b^2)."""
import sys
from fractions import Fraction as F
from functools import lru_cache


@lru_cache(maxsize=None)
def renewal(n, m):
    """cell dict of U^m_n (tuple of tuples)."""
    U = [[F(0)] * n for _ in range(n)]
    if m < 0:
        return tuple(tuple(r) for r in U)
    if m == n - 1:
        return tuple(tuple(F(1) for _ in range(n)) for _ in range(n))
    assert 0 <= m <= n - 2
    K = n - m - 1
    def H(l):
        return F(1) - F(K * K, (n - l) * (n - l + 1)) if 1 <= l <= m + 1 else F(0)
    def add_block(x, y, w):
        for k in range(y - x + 1):
            U[x + k][y - k] += w
    for l in range(1, m + 2):
        add_block(0, l - 1, H(l))
        add_block(n - l, n - 1, H(l))
        for a in range(1, n - l):          # 1 <= a <= n-1-l
            add_block(a, a + l - 1, H(l) - H(l + 1))
    return tuple(tuple(r) for r in U)


def X_matrix(n, lo, hi):
    b = hi + 1
    th = 1 - F(lo * lo, 2 * b * b)
    Uhi = renewal(n, hi)
    Ulo = renewal(n, lo - 1)
    Ub = renewal(b, lo - 1)
    T = n - b + 1                                   # number of windows
    X = [[th * Uhi[i][j] - F(1, 2) * Ulo[i][j] for j in range(n)] for i in range(n)]
    for t in range(T):
        for i in range(b):
            for j in range(b):
                X[t + i][t + j] += ((1 - th) - F(1, 2) * Ub[i][j]) / T
    return X


def check(n, lo, hi):
    X = X_matrix(n, lo, hi)
    R = F((hi + 1) ** 2 - lo * lo, n)
    mn = min(min(r) for r in X)
    for i in range(n):
        for j in range(n):
            assert X[i][j] == X[j][i], ('sym', i, j)
            assert 0 <= X[i][j] <= 1, ('range', i, j, X[i][j])
        assert sum(X[i]) == R, ('row', i)
    for s in range(n):
        want = sum(1 for a in range(lo, hi + 1) if a >= s)
        assert sum(X[i][i + s] for i in range(n - s)) == want, ('run', s)
    return mn


if __name__ == '__main__':
    N1, N2 = int(sys.argv[1]), int(sys.argv[2])
    worst = None
    cnt = 0
    for n in range(N1, N2 + 1):
        for hi in range(n):
            for lo in range(hi + 1):
                mn = check(n, lo, hi)
                cnt += 1
                if (lo, hi) != (0, n - 1) and mn is not None:
                    pos = min((v for r in X_matrix(n, lo, hi) for v in r if v > 0), default=None) if False else None
        print(f'n={n}: all {sum(1 for hi in range(n) for lo in range(hi+1))} (lo,hi) pairs VERIFIED', flush=True)
    print('total cases', cnt)
