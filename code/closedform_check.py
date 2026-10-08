"""Independent check of Lemma 2.1 + Lemma 4.1 + Lemma 5.2 against an independent s-recursion (build_THG, exact
Fractions with rational alpha), comparing with the closed form evaluated in mpmath (60 digits)."""
import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'unif', 'coord'))
from fractions import Fraction as F
import mpmath as mp
from coord_check_dip import build_THG
from construct import amplitudes, a_mp, omega
mp.mp.dps = 60
def sigma(x): return 4 * (mp.digamma(mp.mpf(x + 1) / 2) - mp.digamma(mp.mpf(x) / 2)) / 2 - mp.mpf(2) / x
random.seed(7)
worst = 0; worst52 = 0; cnt = 0
for trial in range(400):
    n = random.randint(6, 300)
    K = random.choice([1, 2, 3, random.randint(1, max(1, (n - 2) // 2))])
    hi = n - 1 - K
    if hi < 1: continue
    lo = random.randint(1, hi); M = n - lo
    use_rule = (2 * hi >= n) and random.random() < 0.7
    if use_rule:
        D = amplitudes(n, lo, hi)
    else:
        D = {hi: F(random.randint(0, 50), random.randint(1, 60))} if 2 * hi >= n else {}
    al = D.get(hi, F(0))
    T, Hf, G, r = build_THG(n, lo, hi, D)
    alm = mp.mpf(al.numerator) / al.denominator
    G_ = M * M - K * K
    for x in range(K + 1, n + 1):
        Phi = 1 - K * K * sigma(x) if x <= M else G_ * sigma(x)
        e = (-1) ** (K + 1) * a_mp(K) + sum((-1) ** y * 2 * (K + 1) * alm / (y * (y - 1)) for y in range(K + 2, min(x, 2 * K + 2) + 1)) + ((-1) ** M * a_mp(M) if x >= M + 1 else 0)
        cf = Phi + (-1) ** x * e
        tv = mp.mpf(T[n - x].numerator) / T[n - x].denominator
        worst = max(worst, abs(cf - tv))
        if use_rule and K >= 2:
            tail = sum((-1) ** (j - 1) * 2 * (K + 1) * alm / ((x + j) * (x + j - 1)) for j in range(1, 2 * K + 3) if K + 2 <= x + j <= 2 * K + 2)
            cf2 = Phi + tail - ((-1) ** (x + M) * a_mp(M) if x <= M else 0)
            worst52 = max(worst52, abs(cf2 - tv))
    cnt += 1
print(f'{cnt} random (n,lo,hi,alpha): max |closed form (Lemma 4.1) - recursion| = {mp.nstr(worst, 5)};  Lemma 5.2 form (rule, K>=2): {mp.nstr(worst52, 5)}')
