"""ALL-d explicit construction of v_k (top k+1 entries of p averaged) as a symmetric marginal of
U (p x p) U^+  ("circulant construction").

T = {0..n-1} (n = k+1), tails j = n..d-1, pi = p[:n], P = sum(pi), Pi = cyclic shift on T,
(Pi^r v)_i = v_{i-r}.
  1. Tail j is assigned a shift r_j (round robin r_j = (j-n) mod n).  Its slots are RELABELLED
     (a permutation of product basis vectors, state stays diagonal):
         value of |i, j>  moves to |i + r_j, j>,   value of |j, i> moves to |j, i + r_j>.
     Row/column i in T then receives p_j pi_{i - r_j}; row/column j is unchanged.
     W_r := total weight of tails with shift r.
  2. beta_r := (1/n - W_r)/P >= 0 (needs W_r <= 1/n), sum_r beta_r = 1; B := sum_r beta_r Pi^r.
  3. Every cyclic diagonal D_s = {(i, i+s mod n)} of T x T (an LC set) is mixed to the diagonal
     B lambda^(s), lambda^(s)_i = pi_i pi_{i+s} (Schur-Horn, exact Chan-Li rotation sequence).
  4. J x J untouched.
Row i in T = P (B pi)_i + sum_r W_r pi_{i-r} = sum_r (P beta_r + W_r) pi_{i-r} = P/n.
"""
import sys
import numpy as np
from lc import build_state_from_sets, check_state


def shifts_round_robin(d, n):
    return {j: (j - n) % n for j in range(n, d)}


def alld_sets(p, k, shifts=None):
    p = np.sort(np.asarray(p, float))[::-1]
    d = len(p)
    n = k + 1
    pi = p[:n]
    P = pi.sum()
    if shifts is None:
        shifts = shifts_round_robin(d, n)
    W = np.zeros(n)
    for j, r in shifts.items():
        W[r] += p[j]
    assert np.all(W <= 1.0 / n + 1e-15), (W, 1.0 / n)
    beta = (1.0 / n - W) / P
    beta = np.maximum(beta, 0.0)
    B = sum(beta[r] * np.roll(np.eye(n), r, axis=0) for r in range(n))   # (B v)_i = sum_r beta_r v_{i-r}
    sets = []
    # tails: relabelling (singleton sets with src != dst)
    for j, r in shifts.items():
        for i in range(n):
            sets.append(([((i + r) % n, j)], [(i, j)], None))
            sets.append(([(j, (i + r) % n)], [(j, i)], None))
    # TT cyclic diagonals, all mixed by the same circulant B
    for s in range(n):
        sl = [(i, (i + s) % n) for i in range(n)]
        lam_s = np.array([pi[i] * pi[(i + s) % n] for i in range(n)])
        sets.append((sl, sl, B @ lam_s))
    return sets, W, beta


if __name__ == "__main__":
    rng = np.random.default_rng(2026)
    ds = [int(a) for a in sys.argv[1:]] or [3, 4, 5, 6, 7, 8, 10, 12]
    worst = 0.0
    count = 0
    for d in ds:
        for k in range(1, d):
            for t in range(4):
                if t == 0:
                    E = np.sort(rng.uniform(0, 1, d)); p = np.exp(-0.02 * E)       # very high T
                elif t == 1:
                    E = np.sort(rng.exponential(1, d)); p = np.exp(-6 * E)         # low T
                elif t == 2:   # obstruction-type point
                    eps = 1e-3
                    p = np.array([1 + eps] * (d - 2) + [1 - (d - 2) * eps] * 2)
                else:
                    p = rng.dirichlet(np.ones(d) * rng.uniform(0.1, 3))
                p = np.sort(np.maximum(p, 1e-12) / p.sum())[::-1]
                p = p / p.sum()
                v = p.copy(); v[:k + 1] = p[:k + 1].mean()
                sets, W, beta = alld_sets(p, k)
                rho = build_state_from_sets(p, sets)
                err = check_state(rho, p, v, verbose=False)
                worst = max(worst, err)
                count += 1
        print(f"d={d}: all k=1..{d-1} x 4 instances validated; running worst error {worst:.2e}", flush=True)
    print(f"TOTAL {count} explicit constructions; worst max(|spec err|,|marg err|) = {worst:.2e}")
