"""Pure image kernel (T=H, G=0): (n-s)T_s + 2 sum_{t=s+1,s+3,..<=a} T_t = 2[s<=a]."""
import sys
from fractions import Fraction as F
def kernel(n, a):
    T = {}
    for s in range(a, -1, -1):
        acc = sum(T.get(t, 0) for t in range(s + 1, a + 2, 2))
        T[s] = (F(2) - 2 * acc) / (n - s)
    return T
if __name__ == "__main__":
    for n in [int(v) for v in sys.argv[1:]]:
        bad = [a for a in range(n - 1) if min(kernel(n, a).values()) < 0]
        print('n', n, 'first a with negative image kernel:', bad[:3])
