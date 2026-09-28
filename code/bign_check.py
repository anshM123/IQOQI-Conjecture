"""Sanity check at large n: exact (Fractions) check of selected intervals with the coordinator's independent builder."""
import sys, time, random
from construct import amplitudes
from check_construct import fast_ok
n = int(sys.argv[1]); cnt = int(sys.argv[2])
random.seed(n)
cases = []
for K in [1, 2, 3, 4, 5, 7, 10, 20, (n - 2) // 2 - 1, (n - 2) // 2, (n - 1) // 2]:
    hi = n - 1 - K
    for lo in sorted(set([hi, hi - 1, hi - 2, max(1, hi - 10), max(1, n // 2), max(1, n // 3), 1])):
        if 1 <= lo <= hi: cases.append((lo, hi))
while len(cases) < cnt:
    hi = random.randint(1, n - 2); lo = random.randint(1, hi); cases.append((lo, hi))
t0 = time.time(); bad = []
for lo, hi in cases:
    D = amplitudes(n, lo, hi)
    r = fast_ok(n, lo, hi, D)
    if r is not True: bad.append((lo, hi, r))
print(f'n={n}: {len(cases)} intervals (incl. K=1..20 near-top, boundary n=2K+2/2K+1, random) exact fast check: failures {bad} ({time.time()-t0:.1f}s)', flush=True)
