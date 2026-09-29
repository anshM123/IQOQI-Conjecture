"""Exact (Fractions) verification of the reduction of Section 3 of main.tex, implemented from the paper's formulas:

  L-D  decomposition  p_i p_j = B_i B_j + sum_{m<k, M<d} omega_{m,M} (chi_{mu,mu} + chi_{m,M})(i,j)
  I1-I5  p_i = sum_M [i<=M] c_M,  B_i = sum_{M>=k} [i<=M] c_M,  p_i - B_i = sum_{m<k}[i<=m] c_m,
         Z = sum_{M>=k} (M+1) c_M,  1 - Z = sum_{m<k} (m+1) c_m
  L-C  run s of the cross C(u,v) (u <= v) is the initial segment of length #{a in [v-u, v] : a >= s}
  L-H  Hall identity L_M = c_M((M+1)(1-Z)^2/Z + F_k), sum_{M>=k} A_M = 1 - Z^2, L > 0 unless p_0 = p_k
  P-W  the configuration F of Proposition W is symmetric, has rows B/Z, and every run is majorized by the
       run of p (x) p   -- for random rational spectra (with ties) and every k, d <= 8
  L-T  Lemma T slopes nu_k >= 0 and sum_k nu_k min(p_i, p_k) = g(p_i) for g(x) = x^t (mpmath), and the thermal
       weights mu_k (sum 1) with Gibbs(beta') = sum_k mu_k w_k.
The interval uniformisations are the ones of Sections 4-6 (renewal squares, J, complements, dipoles; alpha*
rationalised to 1e-30, which is harmless: runs/rows hold for every alpha and the cell margins are positive).
"""
import os
import sys
import random
from fractions import Fraction as F
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_constructions_lib import uniformisation   # noqa: E402

FAILS = []


def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond:
        FAILS.append(name)


def chi(u, v, i, j):
    return 1 if ((i <= u and j <= v) or (i <= v and j <= u)) else 0


def maj(x, lam):
    """x majorized by lam (lam nonincreasing): equal sums and top-k sums of x <= prefix sums of lam."""
    if sum(x) != sum(lam):
        return False
    xs = sorted(x, reverse=True)
    sx = sl = F(0)
    for a_, b_ in zip(xs, lam):
        sx += a_
        sl += b_
        if sx > sl:
            return False
    return True


def random_p(d, rng, ties=False):
    vals = [rng.randint(1, 30) for _ in range(d)]
    if ties and d >= 3:
        j = rng.randrange(d - 1)
        vals[j + 1] = vals[j]
    vals.sort(reverse=True)
    if ties and rng.random() < 0.3:
        vals = [vals[0]] * (1 + rng.randrange(d)) + vals[1:]
        vals = sorted(vals[:d], reverse=True)
    s = sum(vals)
    return [F(v, s) for v in vals]


rng = random.Random(2026)
cases = []
for d in range(1, 9):
    for trial in range(10 if d <= 5 else 5):
        cases.append(random_p(d, rng, ties=(trial % 2 == 1)))
cases.append([F(1, 4)] * 4)                   # fully degenerate
cases.append([F(3, 8), F(3, 8), F(1, 8), F(1, 8)])

UCACHE = {}


def Yget(n, lo, hi):
    key = (n, lo, hi)
    if key not in UCACHE:
        UCACHE[key] = uniformisation(n, lo, hi)
    return UCACHE[key]


allD = allI = allC = allH = allW = True
ninst = 0
for p in cases:
    d = len(p)
    P = p + [F(0)]
    c = [P[m] - P[m + 1] for m in range(d)]
    for k in range(d):
        ninst += 1
        B = [min(p[i], p[k]) for i in range(d)]
        Z = sum(B)
        theta = lambda M: F(1) if M >= k else F(1, 2)
        omega = {(m, M): c[m] * c[M] * theta(M) for m in range(k) for M in range(d)}
        # (I1)-(I5)
        allI &= all(p[i] == sum(c[M] for M in range(d) if i <= M) for i in range(d))
        allI &= all(B[i] == sum(c[M] for M in range(k, d) if i <= M) for i in range(d))
        allI &= all(p[i] - B[i] == sum(c[m] for m in range(k) if i <= m) for i in range(d))
        allI &= Z == sum((M + 1) * c[M] for M in range(k, d))
        allI &= 1 - Z == sum((m + 1) * c[m] for m in range(k))
        # Lemma D
        for i in range(d):
            for j in range(d):
                rhs = B[i] * B[j] + sum(w_ * (chi(min(m, M), min(m, M), i, j) + chi(m, M, i, j))
                                        for (m, M), w_ in omega.items())
                allD &= (p[i] * p[j] == rhs)
        # Lemma C (runs of crosses) for this d
        for u in range(d):
            for v in range(u, d):
                for s in range(d):
                    run = [chi(u, v, i, i + s) for i in range(d - s)]
                    N = len([a_ for a_ in range(v - u, v + 1) if a_ >= s])
                    allC &= run == [1] * N + [0] * (d - s - N)
                allC &= sum(chi(u, v, i, j) for i in range(d) for j in range(d)) == (v + 1)**2 - (v - u)**2
        # Hall
        E = 1 - Z
        Fk = sum((2 * i + 1) * (p[i] - p[k]) for i in range(k))
        A = {M: (1 - Z * Z) * (M + 1) * c[M] / Z for M in range(k, d)}
        bM = {M: sum(omega[(m, M)] * ((M + 1)**2 - (M - m)**2) for m in range(k)) for M in range(k, d)}
        L = {M: A[M] - bM[M] for M in range(k, d)}
        allH &= all(L[M] == c[M] * ((M + 1) * E * E / Z + Fk) for M in range(k, d))
        allH &= all(L[M] >= 0 for M in range(k, d)) and sum(A.values()) == 1 - Z * Z
        Ltot = sum(L.values())
        trivial = all(c[m] == 0 for m in range(k))
        allH &= (Ltot > 0) or trivial
        # Proposition W
        if trivial:
            Fm = [[p[i] * p[j] for j in range(d)] for i in range(d)]
        else:
            f = {M: L[M] / Ltot for M in range(k, d)}

            def flex(lo, hi):
                out = [[F(0)] * d for _ in range(d)]
                for M in range(k, d):
                    Y = Yget(M + 1, lo, hi)
                    for i in range(M + 1):
                        for j in range(M + 1):
                            out[i][j] += f[M] * Y[i][j]
                return out

            Fm = [[B[i] * B[j] for j in range(d)] for i in range(d)]
            for (m, M), w_ in omega.items():
                if w_ == 0:
                    continue
                mu = min(m, M)
                pieces = []
                if M >= k:
                    Yb = Yget(M + 1, M - m, M)
                    big = [[(Yb[i][j] if i <= M and j <= M else F(0)) for j in range(d)] for i in range(d)]
                    pieces.append(big)
                else:
                    pieces.append(flex(max(m, M) - mu, max(m, M)))
                pieces.append(flex(0, mu))
                for G in pieces:
                    for i in range(d):
                        for j in range(d):
                            Fm[i][j] += w_ * G[i][j]
        sym = all(Fm[i][j] == Fm[j][i] for i in range(d) for j in range(d))
        rows = all(sum(Fm[i]) == B[i] / Z for i in range(d))
        runs = all(maj([Fm[i][i + s] for i in range(d - s)], [p[i] * p[i + s] for i in range(d - s)])
                   for s in range(d))
        if not (sym and rows and runs):
            print('   P-W failure', [str(x) for x in p], k, sym, rows, runs)
        allW &= sym and rows and runs

ok(f'(I1)-(I5) telescoping identities ({ninst} instances (p,k))', allI)
ok('Lemma D: p (x) p = B (x) B + sum omega (chi_mu,mu + chi_m,M) exactly', allD)
ok('Lemma C: runs of crosses are initial segments of length #{a in [v-u,v]: a >= s}; |C(u,v)| = (v+1)^2-(v-u)^2', allC)
ok('Lemma H: Hall identity, L_M >= 0, sum A_M = 1 - Z^2, L > 0 unless p_0 = ... = p_k', allH)
ok('Proposition W: symmetric, rows = w_k = B/Z, runs majorized (exact, d <= 8, all k, incl. ties)', allW)

# ------------------------------------------------------------------ Lemma T and thermal weights
mp.mp.dps = 40
allT = True
rng = random.Random(5)
for trial in range(300):
    d = rng.randint(1, 12)
    E = sorted(mp.mpf(rng.uniform(-3, 3)) for _ in range(d))
    if trial % 5 == 0 and d >= 3:
        E[1] = E[0]                                   # degenerate energies
        E[-1] = E[-2]
    beta = mp.mpf(rng.uniform(0.05, 4))
    bp = beta * mp.mpf(rng.choice([0, 1, rng.random()]))
    Zb = sum(mp.e**(-beta * e) for e in E)
    p = [mp.e**(-beta * e) / Zb for e in E]
    Zq = sum(mp.e**(-bp * e) for e in E)
    q = [mp.e**(-bp * e) / Zq for e in E]
    t = bp / beta
    g = lambda z: z**t if z > 0 else (mp.mpf(1) if t == 0 else mp.mpf(0))
    # slopes N_0 = 0, N_k (1<=k<=d-1), N_d
    N = [mp.mpf(0)]
    for kk in range(1, d):
        if p[kk - 1] == p[kk]:
            N.append(N[-1])
        else:
            N.append((g(p[kk - 1]) - g(p[kk])) / (p[kk - 1] - p[kk]))
    N.append(g(p[d - 1]) / p[d - 1])
    nu = [N[kk + 1] - N[kk] for kk in range(d)]
    allT &= all(v > -mp.mpf(10)**-30 for v in nu)
    allT &= all(abs(sum(nu[kk] * min(p[i], p[kk]) for kk in range(d)) - g(p[i])) < mp.mpf(10)**-30 for i in range(d))
    Zk = [sum(min(p[j], p[kk]) for j in range(d)) for kk in range(d)]
    S = sum(g(pi) for pi in p)
    mu = [nu[kk] * Zk[kk] / S for kk in range(d)]
    allT &= abs(sum(mu) - 1) < mp.mpf(10)**-30
    allT &= all(abs(sum(mu[kk] * min(p[i], p[kk]) / Zk[kk] for kk in range(d)) - q[i]) < mp.mpf(10)**-30
                for i in range(d))
ok('Lemma T: nu_k >= 0, sum nu_k min(p_i,p_k) = p_i^t, Gibbs(beta\') = sum mu_k w_k (300 random instances, ties incl.)', allT)

print()
if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)
print('ALL w_k / LEMMA T CHECKS PASSED')
