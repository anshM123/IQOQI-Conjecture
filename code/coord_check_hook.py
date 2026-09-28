"""
Coordinator's INDEPENDENT checker for the Hook Decomposition certificates (does not import any P-STU3 code).
File format: lines "a s i value" (exact fraction), missing entries = 0.
Conditions (n-box, hooks a = 0..n-1, runs s = 0..a, positions i = 0..n-1-s):
  nonneg: x[a][s][i] >= 0 and entries only for s <= a, 0 <= i <= n-1-s
  run   : sum_i x[a][s][i] = 1                                   for all a, s <= a
  rows  : x[a][0][r] + sum_{1<=s<=a} ( x[a][s][r]*[r <= n-1-s] + x[a][s][r-s]*[r >= s] ) = (2a+1)/n   for all a, r
  cells : sum_{a >= s} x[a][s][i] = 1                            for all s, i
"""
import sys
from fractions import Fraction as F
from collections import defaultdict


def check(n, path):
    x = defaultdict(F)
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            a, s, i, v = line.split()
            a, s, i, v = int(a), int(s), int(i), F(v)
            assert 0 <= s <= a < n and 0 <= i <= n - 1 - s, (a, s, i)
            assert v >= 0, ('negative', a, s, i, v)
            x[(a, s, i)] += v
    for a in range(n):
        for s in range(a + 1):
            assert sum(x[(a, s, i)] for i in range(n - s)) == 1, ('run', a, s)
        for r in range(n):
            tot = x[(a, 0, r)]
            for s in range(1, a + 1):
                if r <= n - 1 - s:
                    tot += x[(a, s, r)]
                if r >= s:
                    tot += x[(a, s, r - s)]
            assert tot == F(2 * a + 1, n), ('row', a, r, tot)
    for s in range(n):
        for i in range(n - s):
            assert sum(x[(a, s, i)] for a in range(s, n)) == 1, ('cell', s, i)
    return True


if __name__ == '__main__':
    import os, re, glob
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..',
                                                          'certificates', 'hook_decompositions')
    ok = []
    for path in sorted(glob.glob(os.path.join(d, 'hookdec_n*.txt')), key=lambda f: int(re.search(r'_n(\d+)', f).group(1))):
        n = int(re.search(r'_n(\d+)', path).group(1))
        check(n, path)
        ok.append(n)
    print('Hook decomposition certificates verified exactly for n =', ok)
