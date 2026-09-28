"""Numerical check of Lemma 5 of arXiv:1904.07942 (condition II): for beta' <= beta,
p(beta') in conv{v_0(p(beta)), ..., v_{d-1}(p(beta))}.  Exact formula: in coordinates
x_m = (m+1) p_{m+1} - sum_{i<=m} p_i the simplex condition is
0 <= x_0'/x_0 <= x_1'/x_1 <= ... <= x_{d-2}'/x_{d-2} <= 1 ; we check it and also solve the LP."""
import numpy as np
from scipy.optimize import linprog


def gibbs(E, b):
    w = np.exp(-b * (E - E.min()))
    return w / w.sum()


def vk(p, k):
    v = p.copy(); v[:k + 1] = p[:k + 1].mean(); return v


def in_hull(p, q):
    d = len(p)
    V = np.array([vk(p, k) for k in range(d)]).T
    A = np.vstack([V, np.ones(d)])
    b = np.concatenate([q, [1.0]])
    res = linprog(np.zeros(d), A_eq=A, b_eq=b, bounds=(0, None), method='highs')
    return res.status == 0, (res.x if res.status == 0 else None)


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for d in [3, 4, 5, 6, 8, 10]:
        bad = 0
        N = 4000
        for t in range(N):
            if t % 2:
                E = np.sort(rng.exponential(1, d))
            else:
                E = np.sort(rng.uniform(0, 1, d)) ** rng.uniform(0.2, 4)
            b = 10 ** rng.uniform(-2, 1.5)
            bp = b * rng.uniform(0, 1)
            p = gibbs(E, b); q = gibbs(E, bp)
            ok, a = in_hull(p, q)
            if not ok:
                # tolerance check via ratio criterion
                x = np.array([(m + 1) * p[m + 1] - p[:m + 1].sum() for m in range(d - 1)])
                y = np.array([(m + 1) * q[m + 1] - q[:m + 1].sum() for m in range(d - 1)])
                r = y / np.where(np.abs(x) > 1e-300, x, 1e-300)
                viol = max(0, -r[0], np.max(r[:-1] - r[1:]), r[-1] - 1)
                if viol > 1e-9:
                    bad += 1
        print(f"d={d}: thermal point outside conv(v_k) in {bad}/{N} random instances")
