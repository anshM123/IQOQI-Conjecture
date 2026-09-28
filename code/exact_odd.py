"""Exact certificates for given n (copy of stu3/exact_hookdec.py method, rho-symmetric support search optional)."""
import sys, time
sys.path.insert(0, '../stu3')
from exact_hookdec import exact_certificate
for n in [int(a) for a in sys.argv[1:]]:
    t0 = time.time()
    ok, x, idx = exact_certificate(n)
    with open(f"certs/hookdec_n{n}.txt", "w") as f:
        f.write(f"# exact hook decomposition of the {n}-box: a s i value\n")
        for (a, s, i), j in sorted(idx.items()):
            if x[j] != 0:
                f.write(f"{a} {s} {i} {x[j]}\n")
    print(f"n={n}: verified={ok} ({time.time()-t0:.1f}s)", flush=True)
