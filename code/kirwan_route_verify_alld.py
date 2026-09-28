"""
R021: coordinator's independent check of the all-d circulant construction for v_k (own code).
Marginals after the construction depend only on diagonal weights (coherences live inside cyclic diagonals
D_s = {|i,i+s>}, which have distinct rows and columns). Schur–Horn guarantees a unitary on span(D_s) realising the
diagonal B lambda^(s) because B (circulant, doubly stochastic, beta >= 0) gives B lambda <= lambda (majorisation).
Also checks: beta_r >= 0 (W_r <= 1/n with round-robin shifts), and Lemma 5 (thermal curve in conv{v_k}) via LP.
"""
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(2026)
worst = 0.0
minslack = np.inf
for trial in range(20000):
    d = int(rng.integers(2, 16))
    k = int(rng.integers(0, d))           # v_k: top n = k+1 flattened
    n = k + 1
    mode = rng.integers(3)
    if mode == 0:
        p = rng.dirichlet(np.ones(d) * rng.uniform(0.05, 5))
    elif mode == 1:
        E = np.sort(rng.uniform(0, 10, d)); p = np.exp(-rng.uniform(0.01, 5) * E)
    else:
        p = rng.exponential(size=d) ** rng.uniform(1, 6)
    p = np.sort(p / p.sum())[::-1]
    pi, P = p[:n], p[:n].sum()
    tails = list(range(n, d)); Q = p[n:].sum()
    shift = {j: (j - n) % n for j in tails}
    W = np.zeros(n)
    for j in tails:
        W[shift[j]] += p[j]
    beta = (1.0 / n - W) / P
    minslack = min(minslack, beta.min())
    # build diagonal weights after construction and compute marginals
    rowA = np.zeros(d); colB = np.zeros(d)
    # TT sector: diagonal s, position i (state |i, i+s>) gets (B lam^(s))_i = sum_r beta_r lam^(s)_{i-r}
    for s in range(n):
        lam = np.array([pi[i] * pi[(i + s) % n] for i in range(n)])
        Blam = np.array([sum(beta[r] * lam[(i - r) % n] for r in range(n)) for i in range(n)])
        assert np.all(np.sort(Blam)[::-1].cumsum() <= np.sort(lam)[::-1].cumsum() + 1e-15)   # majorisation
        for i in range(n):
            rowA[i] += Blam[i]; colB[(i + s) % n] += Blam[i]
    # tails: |i j> -> |i + r_j, j>, |j i> -> |j, i + r_j>
    for j in tails:
        for i in range(n):
            rowA[(i + shift[j]) % n] += pi[i] * p[j]; colB[j] += pi[i] * p[j]
            rowA[j] += p[j] * pi[i]; colB[(i + shift[j]) % n] += p[j] * pi[i]
        for jj in tails:
            rowA[j] += p[j] * p[jj]; colB[jj] += p[j] * p[jj]
    vk = np.concatenate([np.full(n, P / n), p[n:]])
    worst = max(worst, np.abs(rowA - vk).max(), np.abs(colB - vk).max())
print(f"20000 random (d<=15, all k, varied spectra): max marginal error {worst:.2e}; min beta_r {minslack:.3e} (must be >= 0)")

# Lemma 5: p(beta') in conv{v_0..v_{d-1}} for beta' in [0, beta]
bad = 0
for trial in range(3000):
    d = int(rng.integers(2, 12))
    E = np.sort(rng.uniform(0, 5, d)); b = rng.uniform(0.05, 6)
    p = np.exp(-b * E); p /= p.sum()
    V = []
    for kk in range(d):
        n = kk + 1
        V.append(np.concatenate([np.full(n, p[:n].sum() / n), p[n:]]))
    V = np.array(V).T
    bp = rng.uniform(0, b)
    q = np.exp(-bp * E); q /= q.sum()
    res = linprog(np.zeros(d), A_eq=np.vstack([V, np.ones(d)]), b_eq=np.r_[q, 1], bounds=(0, None), method='highs')
    bad += res.status != 0
print(f"Lemma 5 LP: thermal point outside conv(v_k) in {bad}/3000 random instances")
