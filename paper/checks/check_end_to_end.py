"""End-to-end numerical check of Theorem 1 of main.tex, built from the paper's constructions only (numpy, float64):

  random Hermitian H on C^d (NOT diagonal), beta > 0, 0 <= beta' <= beta
  -> spectral decomposition H = V diag(E) V^dagger, E sorted increasingly (local-unitary reduction, Sec. 2)
  -> p = Gibbs(E, beta), weights mu_k of Lemma T, configurations F_k of Proposition W (with the interval
     uniformisations of Sections 4-6), F = sum_k mu_k F_k                      (Sections 3.3-3.6)
  -> on every diagonal D of the d x d grid a real Schur-Horn rotation G_D (Chan-Li style algorithm, as in
     SchurHorn.lean) with diag(G_D diag(p (x) p |_D) G_D^T) = F|_D; O = direct sum of the G_D   (Prop. 3.3)
  -> U = (V (x) V) O (V (x) V)^dagger
and checks that BOTH marginals of U (tau_beta (x) tau_beta) U^dagger equal tau_beta'(H), that U is unitary, and
that O is real orthogonal.  d = 1..6, several hundred random instances, including degenerate spectra.
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_constructions_lib import uniformisation_float  # noqa: E402

rng = np.random.default_rng(20260928)
FAILS = []


def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond:
        FAILS.append(name)


def schur_horn(lam, x, tol=1e-13):
    """Real orthogonal G with diag(G diag(lam) G^T) = x, assuming x majorised by lam (Chan-Li induction)."""
    N = len(lam)
    A = np.diag(np.array(lam, dtype=float))
    G = np.eye(N)
    U = list(range(N))
    scale = max(1.0, max(abs(v) for v in lam))
    while len(U) > 1:
        i0 = max(U, key=lambda i: x[i])
        a = x[i0]
        j1 = max(U, key=lambda j: A[j, j])
        m1 = A[j1, j1]
        assert m1 >= a - tol * scale, 'majorisation violated'
        if m1 - a > tol * scale:
            cands = [j for j in U if j != j1 and A[j, j] <= a + tol * scale]
            j2 = max(cands, key=lambda j: A[j, j])
            m2 = A[j2, j2]
            c2 = min(max((a - m2) / (m1 - m2), 0.0), 1.0)
            c, s = np.sqrt(c2), np.sqrt(1.0 - c2)
            R = np.eye(N)
            R[j1, j1], R[j1, j2], R[j2, j1], R[j2, j2] = c, s, -s, c
            A = R @ A @ R.T
            G = R @ G
        if j1 != i0:
            P = np.eye(N)
            P[[j1, i0]] = P[[i0, j1]]
            A = P @ A @ P.T
            G = P @ G
        U.remove(i0)
    return G


UC = {}


def Y(n, lo, hi):
    if (n, lo, hi) not in UC:
        UC[(n, lo, hi)] = np.array(uniformisation_float(n, lo, hi))
    return UC[(n, lo, hi)]


def wk_config(p, k):
    d = len(p)
    P = list(p) + [0.0]
    c = [P[m] - P[m + 1] for m in range(d)]
    B = np.minimum(p, p[k])
    Z = B.sum()
    Fm = np.outer(B, B)
    if all(abs(c[m]) < 1e-15 for m in range(k)) or k == 0:
        return np.outer(p, p) if k > 0 else Fm, B / Z
    theta = lambda M: 1.0 if M >= k else 0.5
    A = {M: (1 - Z * Z) * (M + 1) * c[M] / Z for M in range(k, d)}
    bM = {M: sum(c[m] * c[M] * ((M + 1)**2 - (M - m)**2) for m in range(k)) for M in range(k, d)}
    L = {M: A[M] - bM[M] for M in range(k, d)}
    Lt = sum(L.values())
    f = {M: L[M] / Lt for M in range(k, d)}

    def emb(Ym):
        out = np.zeros((d, d))
        n = Ym.shape[0]
        out[:n, :n] = Ym
        return out

    def flex(lo, hi):
        return sum(f[M] * emb(Y(M + 1, lo, hi)) for M in range(k, d))

    for m in range(k):
        for M in range(d):
            w_ = c[m] * c[M] * theta(M)
            if w_ == 0:
                continue
            mu = min(m, M)
            if M >= k:
                Fm = Fm + w_ * (emb(Y(M + 1, M - m, M)) + flex(0, mu))
            else:
                Fm = Fm + w_ * (flex(max(m, M) - mu, max(m, M)) + flex(0, mu))
    return Fm, B / Z


def lemmaT_weights(p, t):
    d = len(p)
    g = (lambda z: 1.0) if t == 0 else (lambda z: z**t)
    N = [0.0]
    for k in range(1, d):
        N.append(N[-1] if p[k - 1] == p[k] else (g(p[k - 1]) - g(p[k])) / (p[k - 1] - p[k]))
    N.append(g(p[d - 1]) / p[d - 1])
    nu = np.array([N[k + 1] - N[k] for k in range(d)])
    Zk = np.array([np.minimum(p, p[k]).sum() for k in range(d)])
    S = sum(g(v) for v in p)
    return nu * Zk / S


def build_O(p, Fm):
    d = len(p)
    O = np.zeros((d * d, d * d))
    idx = lambda i, j: i * d + j
    for s in range(-(d - 1), d):
        cells = [(i, i + s) for i in range(d) if 0 <= i + s < d]
        lam = [p[i] * p[j] for (i, j) in cells]
        x = [Fm[i, j] for (i, j) in cells]
        G = schur_horn(lam, x)
        for a_, ca in enumerate(cells):
            for b_, cb in enumerate(cells):
                O[idx(*ca), idx(*cb)] = G[a_, b_]
    return O


def ptrace_B(rho, d):
    return np.einsum('ijkj->ik', rho.reshape(d, d, d, d))


def ptrace_A(rho, d):
    return np.einsum('ijil->jl', rho.reshape(d, d, d, d))


def gibbs_matrix(H, b):
    ev, V = np.linalg.eigh(H)
    w_ = np.exp(-b * (ev - ev.min()))
    return (V * (w_ / w_.sum())) @ V.conj().T


maxerr = 0.0
maxorth = 0.0
ninst = 0
allmaj = True
for d in range(1, 7):
    for trial in range(60 if d <= 4 else 30):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        H = (X + X.conj().T) / 2
        if trial % 6 == 5 and d >= 3:                 # degenerate energies
            ev, V = np.linalg.eigh(H)
            ev[1] = ev[0]
            H = (V * ev) @ V.conj().T
        E, V = np.linalg.eigh(H)                       # E sorted increasingly
        beta = rng.uniform(0.1, 3.0)
        bp = beta * rng.choice([0.0, 1.0, rng.uniform()])
        p = np.exp(-beta * (E - E.min()))
        p /= p.sum()
        t = bp / beta
        mu = lemmaT_weights(p, t)
        Fm = np.zeros((d, d))
        q = np.zeros(d)
        for k in range(d):
            Fk, wk = wk_config(p, k)
            Fm += mu[k] * Fk
            q += mu[k] * wk
        # runs majorised (numerically)
        for s in range(d):
            xs = np.sort([Fm[i, i + s] for i in range(d - s)])[::-1]
            ls = np.array([p[i] * p[i + s] for i in range(d - s)])
            allmaj &= np.all(np.cumsum(xs) <= np.cumsum(ls) + 1e-12) and abs(xs.sum() - ls.sum()) < 1e-12
        O = build_O(p, Fm)
        maxorth = max(maxorth, np.abs(O @ O.T - np.eye(d * d)).max())
        W = np.kron(V, V)
        U = W @ O @ W.conj().T
        tau = gibbs_matrix(H, beta)
        taup = gibbs_matrix(H, bp)
        rho = U @ np.kron(tau, tau) @ U.conj().T
        err = max(np.abs(ptrace_B(rho, d) - taup).max(), np.abs(ptrace_A(rho, d) - taup).max(),
                  np.abs(q - np.exp(-bp * (E - E.min())) / np.exp(-bp * (E - E.min())).sum()).max())
        maxerr = max(maxerr, err)
        ninst += 1
ok(f'runs of F = sum mu_k F_k majorised by the runs of p(x)p ({ninst} instances)', allmaj)
ok(f'O real orthogonal (max |O O^T - 1| = {maxorth:.2e})', maxorth < 1e-10)
ok(f'both marginals of U(tau x tau)U^dag equal tau_beta\'(H) for random NON-diagonal H, d <= 6 '
   f'(max error {maxerr:.2e})', maxerr < 1e-10)

print()
if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)
print('ALL END-TO-END CHECKS PASSED')
