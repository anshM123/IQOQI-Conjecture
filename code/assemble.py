"""Assemble exact hook decompositions for all n <= NMAX whose odd part has a certificate:
   odd n <= 20: ../stu3/hookdec_n{n}.txt ; odd 21..39: certs/hookdec_n{n}.txt ; even n: DOUBLING of n/2 (recursively).
   Writes certs/final_n{n}.txt and verifies each file with the coordinator's INDEPENDENT checker (stu3/coord_check_hook.py)."""
import sys, os, time
sys.path.insert(0, '../stu3')
from coord_check_hook import check as indep_check
from hookio import load, save
from doubling import double

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
cache = {}
def get(n):
    if n in cache: return cache[n]
    if n % 2 == 0:
        Ys = double(get(n // 2)); how = f'doubling of {n//2}'
    else:
        p = f'../stu3/hookdec_n{n}.txt' if n <= 20 else f'certs/hookdec_n{n}.txt'
        if not os.path.exists(p): raise FileNotFoundError(p)
        Ys = load(p, n); how = 'LP certificate'
    cache[n] = Ys; get.how[n] = how
    return Ys
get.how = {}

done, missing = [], []
for n in range(1, NMAX + 1):
    t = time.time()
    try:
        Ys = get(n)
    except FileNotFoundError as e:
        missing.append(n); continue
    path = f'certs/final_n{n}.txt'
    save(path, Ys, note=f'({get.how[n]})')
    ok = indep_check(n, path)
    done.append(n)
    print(f'n={n:3d} [{get.how[n]}] independent exact check: {ok} ({time.time()-t:.1f}s)', flush=True)
print('verified n:', done)
print('missing (odd part without certificate):', missing)
