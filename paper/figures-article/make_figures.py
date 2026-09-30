"""Figures for the manuscript "Correlations between quantum systems can always be created at minimal energy cost".

All data are computed from the explicit construction of the paper (the interval uniformisations are taken from the
library of the independent checks, which implements the paper's formulas), in double precision.
Run:  python make_figures.py      (writes figures/fig1.pdf, fig2.pdf, fig3.pdf and prints the numbers quoted in the text)
"""
import os
import sys

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Rectangle, FancyArrowPatch
from matplotlib.colors import LinearSegmentedColormap

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'checks'))
from check_constructions_lib import uniformisation_float  # noqa: E402

OUT = os.path.join(HERE, 'figures')
os.makedirs(OUT, exist_ok=True)

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.sans-serif': ['Arial', 'Helvetica', 'DejaVu Sans'],
    'font.size': 7, 'axes.labelsize': 7, 'axes.titlesize': 7, 'xtick.labelsize': 6, 'ytick.labelsize': 6,
    'legend.fontsize': 6, 'axes.linewidth': 0.6, 'xtick.major.width': 0.6, 'ytick.major.width': 0.6,
    'xtick.major.size': 2.5, 'ytick.major.size': 2.5, 'pdf.fonttype': 42, 'savefig.dpi': 600,
})
C_BLUE, C_RED, C_ORANGE, C_GREEN, C_GREY = '#0072B2', '#D55E00', '#E69F00', '#009E73', '#8C8C8C'
MM = 1 / 25.4


def panel_label(ax, s, x=-0.02, y=1.02):
    ax.text(x, y, s, transform=ax.transAxes, fontsize=8, fontweight='bold', va='bottom', ha='right')


# ------------------------------------------------------------------------------------------------ construction
def schur_horn(lam, x, tol=1e-13):
    """Real orthogonal G with diag(G diag(lam) G^T) = x for x majorised by lam (Chan-Li induction)."""
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


_UC = {}


def Y(n, lo, hi):
    if (n, lo, hi) not in _UC:
        _UC[(n, lo, hi)] = np.array(uniformisation_float(n, lo, hi))
    return _UC[(n, lo, hi)]


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
    bM = {M: sum(c[m] * c[M] * ((M + 1) ** 2 - (M - m) ** 2) for m in range(k)) for M in range(k, d)}
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
    g = (lambda z: 1.0) if t == 0 else (lambda z: z ** t)
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


def stu(E, beta, betap):
    """Explicit symmetrically thermalizing unitary for H = diag(E) (E sorted increasingly)."""
    p = np.exp(-beta * (E - E.min()))
    p /= p.sum()
    mu = lemmaT_weights(p, betap / beta)
    Fm = np.zeros((len(E), len(E)))
    for k in range(len(E)):
        Fk, _ = wk_config(p, k)
        Fm += mu[k] * Fk
    return build_O(p, Fm), Fm, p


def ptrace_B(rho, d):
    return np.einsum('ijkj->ik', rho.reshape(d, d, d, d))


def ptrace_A(rho, d):
    return np.einsum('ijil->jl', rho.reshape(d, d, d, d))


def gibbs(E, b):
    w_ = np.exp(-b * (E - E.min()))
    return w_ / w_.sum()


def S_bits(r):
    ev = np.linalg.eigvalsh((r + r.conj().T) / 2)
    ev = ev[ev > 1e-15]
    return float(-(ev * np.log2(ev)).sum())


# ------------------------------------------------------------------------------------------------ Figure 1
E = np.array([0.0, 0.62, 1.05, 1.83, 2.41])      # an irregular (not equally spaced) five-level spectrum
d = len(E)
beta = 1.3
tau = np.diag(gibbs(E, beta))
rho0 = np.kron(tau, tau)
H2 = np.kron(np.diag(E), np.eye(d)) + np.kron(np.eye(d), np.diag(E))
E0 = np.trace(H2 @ rho0).real
S0 = 2 * S_bits(tau)


def point(U):
    r = U @ rho0 @ U.conj().T
    rA, rB = ptrace_B(r, d), ptrace_A(r, d)
    return np.trace(H2 @ r).real - E0, S_bits(rA) + S_bits(rB) - S0


bgrid = np.linspace(0, beta, 400)
front = np.array([(2 * (E @ gibbs(E, b)) - 2 * (E @ gibbs(E, beta)),
                   2 * S_bits(np.diag(gibbs(E, b))) - S0) for b in bgrid])

rng = np.random.default_rng(7)
pts = []
for _ in range(2500):
    X = rng.normal(size=(d * d, d * d)) + 1j * rng.normal(size=(d * d, d * d))
    K = (X + X.conj().T) / 2
    eps = rng.uniform(0.0, 0.9) ** 1.5
    w_, V = np.linalg.eigh(K)
    U = (V * np.exp(-1j * eps * w_)) @ V.conj().T
    pts.append(point(U))
pts = np.array(pts)

ratios = [0.85, 0.65, 0.45, 0.25, 0.0]
stu_pts, stu_err, orth_err = [], 0.0, 0.0
for rt in ratios:
    O, Fm, p = stu(E, beta, rt * beta)
    orth_err = max(orth_err, np.abs(O @ O.T - np.eye(d * d)).max())
    r = O @ rho0 @ O.T
    tgt = np.diag(gibbs(E, rt * beta))
    stu_err = max(stu_err, np.abs(ptrace_B(r, d) - tgt).max(), np.abs(ptrace_A(r, d) - tgt).max())
    stu_pts.append(point(O))
stu_pts = np.array(stu_pts)
print(f'[fig1] d = {d}, beta = {beta}: STU marginal error {stu_err:.1e}, orthogonality error {orth_err:.1e}')
for rt, (x, y) in zip(ratios, stu_pts):
    b = rt * beta
    xf = 2 * (E @ gibbs(E, b)) - 2 * (E @ gibbs(E, beta))
    yf = 2 * S_bits(np.diag(gibbs(E, b))) - S0
    print(f"[fig1] beta'/beta = {rt:.2f}: dE = {x:.6f} (bound curve {xf:.6f}), dI = {y:.6f} bits (bound {yf:.6f})")
# largest ratio of created correlations to the bound, among the random unitaries, at comparable energy
fr_I = np.interp(pts[:, 0], front[::-1, 0], front[::-1, 1])
print(f'[fig1] random unitaries: max (dI - bound) = {np.max(pts[:, 1] - fr_I):.2e} bits (must be <= 0)')

fig = plt.figure(figsize=(180 * MM, 62 * MM))
axA = fig.add_axes([0.005, 0.04, 0.47, 0.86])
axB = fig.add_axes([0.575, 0.17, 0.41, 0.74])

# (a) schematic
axA.set_xlim(0, 10)
axA.set_ylim(0, 4.3)
axA.axis('off')
pT = gibbs(E, beta)
pTp = gibbs(E, 0.45 * beta)


def ladder(x0, pops, col, label, sub):
    for i in range(d):
        y = 0.55 + E[i] * 1.12
        axA.plot([x0, x0 + 0.9], [y, y], color='k', lw=0.8)
        axA.add_patch(Rectangle((x0 + 0.95, y - 0.07), 1.6 * pops[i], 0.14, color=col, lw=0))
    axA.text(x0 + 0.45, 3.55, label, ha='center', va='bottom', fontsize=7)
    axA.text(x0 + 0.45, 0.12, sub, ha='center', va='bottom', fontsize=6.5)


ladder(0.2, pT, C_BLUE, 'A', r'$\tau_\beta$')
ladder(2.35, pT, C_BLUE, 'B', r'$\tau_\beta$')
axA.add_patch(FancyBboxPatch((4.55, 1.05), 0.95, 1.6, boxstyle='round,pad=0.05', fc='#F2F2F2', ec='k', lw=0.8))
axA.text(5.03, 1.85, r'$U$', ha='center', va='center', fontsize=10)
axA.add_patch(FancyArrowPatch((4.05, 1.85), (4.5, 1.85), arrowstyle='-|>', mutation_scale=7, lw=0.8, color='k'))
axA.add_patch(FancyArrowPatch((5.55, 1.85), (6.0, 1.85), arrowstyle='-|>', mutation_scale=7, lw=0.8, color='k'))
ladder(6.15, pTp, C_RED, 'A', r"$\tau_{\beta'}$")
ladder(8.3, pTp, C_RED, 'B', r"$\tau_{\beta'}$")
xs = np.linspace(7.35, 8.25, 60)
axA.plot(xs, 3.25 + 0.07 * np.sin(2 * np.pi * (xs - 7.35) / 0.18), color=C_ORANGE, lw=0.9)
axA.text(7.8, 3.45, r'$\Delta I$', ha='center', fontsize=7, color=C_ORANGE)
axA.text(2.0, 4.0, r'temperature $T$', ha='center', fontsize=7)
axA.text(7.95, 4.0, r"$T'>T$, same for both", ha='center', fontsize=7)
panel_label(axA, 'a', x=0.02, y=0.98)

# (b) energy-correlation plane
axB.fill_between(front[:, 0], front[:, 1], front[:, 1].max() * 1.35, color='#F4E1D8', lw=0, zorder=0)
axB.text(0.62 * front[:, 0].max(), 0.93 * front[:, 1].max() * 1.12, 'forbidden', color=C_RED, fontsize=6.5,
         ha='center')
axB.scatter(pts[:, 0], pts[:, 1], s=1.2, color=C_GREY, alpha=0.45, lw=0, zorder=1,
            label='random global unitaries')
axB.plot(front[:, 0], front[:, 1], color='k', lw=1.0, zorder=2,
         label=r"bound $2[S(\tau_{\beta'})-S(\tau_\beta)]$")
axB.scatter(stu_pts[:, 0], stu_pts[:, 1], s=16, marker='*', color=C_BLUE, zorder=3, lw=0,
            label='explicit STUs (this work)')
axB.set_xlim(0, front[:, 0].max() * 1.02)
axB.set_ylim(0, front[:, 1].max() * 1.12)
axB.set_xlabel(r'energy invested $\Delta E$ (units of $\epsilon$)')
axB.set_ylabel(r'correlations created $\Delta I$ (bits)')
axB.legend(loc='lower right', frameon=False, handletextpad=0.4, borderaxespad=0.2)
panel_label(axB, 'b', x=-0.1)
fig.savefig(os.path.join(OUT, 'fig1.pdf'))
plt.close(fig)

# ------------------------------------------------------------------------------------------------ Figure 2
rt2 = 0.5
O2, F2, p2 = stu(E, beta, rt2 * beta)
order = []
blocks = []
for t in range(-(d - 1), d):
    cells = [(i, i + t) for i in range(d) if 0 <= i + t < d]
    blocks.append(len(cells))
    order += [i * d + j for (i, j) in cells]
Oo = O2[np.ix_(order, order)]
r2 = O2 @ rho0 @ O2.T
margA = np.diag(ptrace_B(r2, d))
margB = np.diag(ptrace_A(r2, d))
print(f"[fig2] beta'/beta = {rt2}: max |marginal - Gibbs| = "
      f"{max(np.abs(margA - gibbs(E, rt2 * beta)).max(), np.abs(margB - gibbs(E, rt2 * beta)).max()):.1e}")
print(f'[fig2] nonzero entries of O: {int((np.abs(O2) > 1e-12).sum())} of {d ** 4}; block sizes {blocks}')

fig = plt.figure(figsize=(180 * MM, 56 * MM))
ax1 = fig.add_axes([0.035, 0.16, 0.2, 0.72])
ax2 = fig.add_axes([0.30, 0.16, 0.2, 0.72])
ax3 = fig.add_axes([0.56, 0.16, 0.18, 0.72])
cax3 = fig.add_axes([0.745, 0.16, 0.008, 0.72])
ax4 = fig.add_axes([0.83, 0.16, 0.16, 0.72])

cm_div = plt.get_cmap('RdBu')
for i in range(d):
    for j in range(d):
        t = j - i
        ax1.add_patch(Rectangle((j, d - 1 - i), 0.96, 0.96, color=cm_div(0.5 + t / (2.4 * (d - 1))), lw=0))
        ax1.text(j + 0.48, d - 1 - i + 0.48, f'{t:+d}' if t else '0', ha='center', va='center', fontsize=5.5)
for (i, j) in [(0, 0), (1, 1), (2, 2)]:
    ax1.add_patch(FancyArrowPatch((j + 0.75, d - 1 - i + 0.25), (j + 1.21, d - 2 - i + 0.71),
                                  arrowstyle='<|-|>', mutation_scale=5, lw=0.7, color='k'))
ax1.set_xlim(-0.05, d)
ax1.set_ylim(-0.05, d)
ax1.set_xticks(np.arange(d) + 0.48)
ax1.set_xticklabels(range(d))
ax1.set_yticks(np.arange(d) + 0.48)
ax1.set_yticklabels(range(d)[::-1])
ax1.set_xlabel('level $j$ of B')
ax1.set_ylabel('level $i$ of A')
ax1.set_title(r'diagonals $t=j-i$', pad=3)
for s in ax1.spines.values():
    s.set_visible(False)
ax1.tick_params(length=0)
panel_label(ax1, 'a', x=-0.12)

ax2.imshow(np.abs(Oo), cmap='Greys', vmin=0, vmax=1, interpolation='nearest')
edge = np.cumsum([0] + blocks) - 0.5
for e in edge:
    ax2.axhline(e, color=C_BLUE, lw=0.3)
    ax2.axvline(e, color=C_BLUE, lw=0.3)
ax2.set_xticks([])
ax2.set_yticks([])
ax2.set_title(r'$|O|$, basis grouped by $t$', pad=3)
ax2.set_xlabel(r'$t=-4,\dots,+4$ (blocks of size $d-|t|$)')
panel_label(ax2, 'b', x=-0.05)

im3 = ax3.imshow(F2, cmap='viridis', interpolation='nearest')
ax3.set_xticks(range(d))
ax3.set_yticks(range(d))
ax3.set_xlabel('level $j$ of B')
ax3.set_ylabel('level $i$ of A')
ax3.set_title(r"populations $\langle ij|\rho'|ij\rangle$", pad=3)
cb = fig.colorbar(im3, cax=cax3)
cb.ax.tick_params(labelsize=5, length=1.5)
cb.outline.set_linewidth(0.4)
panel_label(ax3, 'c', x=-0.1)

xk = np.arange(d)
ax4.bar(xk - 0.2, gibbs(E, beta), width=0.38, color=C_BLUE, label=r'initial $\tau_\beta$')
ax4.bar(xk + 0.2, margA, width=0.38, color=C_RED, label=r"marginals of $\rho'$")
ax4.plot(xk + 0.2, gibbs(E, rt2 * beta), 'k_', ms=6, mew=0.9, label=r"Gibbs at $\beta'=\beta/2$")
ax4.set_xticks(xk)
ax4.set_xlabel('level')
ax4.set_ylabel('population')
ax4.legend(frameon=False, loc='upper right', handlelength=1.0)
panel_label(ax4, 'd', x=-0.12)
fig.savefig(os.path.join(OUT, 'fig2.pdf'))
plt.close(fig)

# ------------------------------------------------------------------------------------------------ Figure 3
fig = plt.figure(figsize=(180 * MM, 78 * MM))
axF = fig.add_axes([0.0, 0.0, 0.64, 1.0])
axY = fig.add_axes([0.70, 0.2, 0.235, 0.66])
caxY = fig.add_axes([0.945, 0.2, 0.008, 0.66])
axF.set_xlim(0, 100)
axF.set_ylim(0, 63.5)
axF.axis('off')

steps = [
    ('STUs exist for every $d$, every Hermitian $H$, every $0\\leq\\beta\'\\leq\\beta$',
     'stu_exists_hermitian', 'spectral theorem, local unitary $V\\otimes V$'),
    ('Sorted diagonal case $H=\\mathrm{diag}(E)$; target $q=\\gamma_{\\beta\'}(E)$',
     'stu_exists_unconditional', 'Schur-Horn on the $2d-1$ diagonals $j-i=t$'),
    ('Reach$(p)$: row sums of admissible configurations; convex',
     'ReachTri.orthogonal, .convex', 'Lemma T: $q$ = mixture of clipped points $w_k$'),
    ('Every clipped point $w_k$ is reachable',
     'wkU_reach', 'Young-diagram decomposition, Hall identity'),
    ('Interval uniformisations exist for all boxes $n$ and all $[\\ell,h]$',
     'intervalUnifAll_all', 'renewal squares, T/H/G matrix, one dipole'),
    ('Facts F1-F6 on $a(K)=4K^2(-1)^K(\\ln2-\\sum_{i\\leq K}\\frac{(-1)^{i-1}}{i})+1-2K$',
     'factF1 ... factF6', ''),
]
ytop = 55
for k, (txt, leanname, via) in enumerate(steps):
    y = ytop - k * 9.6
    axF.add_patch(FancyBboxPatch((3, y - 3.3), 60, 6.6, boxstyle='round,pad=0.4', fc='#EEF4FA' if k else '#DCE9F5',
                                 ec=C_BLUE, lw=0.7))
    axF.text(5, y, txt, va='center', ha='left', fontsize=6.3)
    axF.add_patch(FancyBboxPatch((67, y - 2.6), 30, 5.2, boxstyle='round,pad=0.3', fc='#F3F3F3', ec=C_GREY, lw=0.5))
    axF.text(82, y, leanname, va='center', ha='center', fontsize=5.6, family='monospace')
    axF.plot([63.6, 66.6], [y, y], color=C_GREY, lw=0.5, ls=':')
    if k < len(steps) - 1:
        axF.add_patch(FancyArrowPatch((20, y - 3.9), (20, y - 5.7), arrowstyle='<|-', mutation_scale=6, lw=0.7,
                                      color='k'))
        axF.text(22, y - 4.8, via, va='center', ha='left', fontsize=5.4, style='italic', color='#333333')
axF.text(82, 61.6, 'Lean 4 + Mathlib', ha='center', fontsize=6.5, fontweight='bold')
axF.text(33, 61.6, 'proof chain', ha='center', fontsize=6.5, fontweight='bold')
axF.text(50, 0.6, 'formal check: standard axioms only (propext, Classical.choice, Quot.sound); no sorry',
         ha='center', fontsize=5.8, color='#333333')
panel_label(axF, "a", x=0.03, y=0.955)

n_ex, lo_ex, hi_ex = 9, 2, 5
Yex = np.array(uniformisation_float(n_ex, lo_ex, hi_ex))
imY = axY.imshow(Yex, cmap='magma_r', vmin=0, vmax=1, interpolation='nearest')
axY.set_xticks(range(n_ex))
axY.set_yticks(range(n_ex))
axY.tick_params(labelsize=5)
axY.set_title(f'interval uniformisation, $n={n_ex}$, $[\\ell,h]=[{lo_ex},{hi_ex}]$', pad=3, fontsize=6.3)
rows = Yex.sum(axis=1)
runs = [sum(Yex[i, i + s] for i in range(n_ex - s)) for s in range(n_ex)]
target_runs = [sum(1 for a_ in range(lo_ex, hi_ex + 1) if a_ >= s) for s in range(n_ex)]
axY.set_xlabel(f'row sums all $= {rows[0]:.4f}$; run sums $=(4,4,4,3,2,1,0,\\dots)$', fontsize=5.6)
cbY = fig.colorbar(imY, cax=caxY)
cbY.ax.tick_params(labelsize=5, length=1.5)
cbY.outline.set_linewidth(0.4)
panel_label(axY, 'b', x=-0.08)
print(f'[fig3] Y({n_ex},[{lo_ex},{hi_ex}]): entries in [{Yex.min():.4f}, {Yex.max():.4f}], symmetric '
      f'{np.abs(Yex - Yex.T).max():.1e}, row sums {rows.min():.12f}..{rows.max():.12f} '
      f'(target {sum(2 * a_ + 1 for a_ in range(lo_ex, hi_ex + 1)) / n_ex:.12f}), runs {np.round(runs, 12)} '
      f'(target {target_runs})')
fig.savefig(os.path.join(OUT, 'fig3.pdf'))
plt.close(fig)
print('figures written to', OUT)
