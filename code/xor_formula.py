"""Closed form of the iterated doubling from the 1-box (n = 2^k): verify against doubling.py exactly."""
from fractions import Fraction as F
from doubling import double
from hookio import check

def iterated(k):
    Ys = [[[F(1)]]]
    for _ in range(k): Ys = double(Ys)
    return Ys

def formula(k, b, i, j):
    """scan bits from the top; f = 'complement flag'.  same bit: factor 1/2, flag <- bit of b ;
       different bit: need (b_t xor f) = 1, flag unchanged."""
    val = F(1); f = 0
    for t in range(k - 1, -1, -1):
        bt = (b >> t) & 1; it = (i >> t) & 1; jt = (j >> t) & 1
        if it == jt:
            val /= 2; f = bt
        else:
            if (bt ^ f) != 1: return F(0)
    return val

for k in range(0, 6):
    n = 2 ** k; Ys = iterated(k)
    ok = all(Ys[b][i][j] == formula(k, b, i, j) for b in range(n) for i in range(n) for j in range(n))
    print('n =', n, 'formula == iterated doubling:', ok, ' check:', check(Ys)[0])
