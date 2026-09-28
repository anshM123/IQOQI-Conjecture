# P-STU4 research log (Kirwan-free proof: thermal targets are symmetric marginals of the orbit of diag(p⊗p))

## 2026-09-28 session start
- Read stu/REPORT.md, stu/LOG.md, stu2/LOG.md, thermal_construction.py, lcs.py, cert_loopcirc.py, stu3/LOG.md (P-STU3
  works on C2 = M(p) ⊂ R_tri; I avoid its files).
- Goal: for each (d, p, t) an explicit LC construction (cell permutation + LC partition + majorised diagonals) with
  rows = cols = q_t ∝ p^t, with an analytic proof valid for all d.
- Exp1 (tri_mlr.py): tri-run structure with MONOTONE runs (x^s non-increasing along run) + MLR or prefix: infeasible for
  small t (u unreachable with monotone tri-runs: row d-1 is the minimum of each run). Dead end.
- Exp1b (structs.py): anti-cyclic diagonals {i+j = s mod d} (self-transposed LC sets): 25-35% infeasible. Dead end.
- Exp2 (cyc_mlr2.py, verify_mlr.py) KEY: cyclic diagonals D_s = {(i,i+s mod d)} (sorted cyclic order), symmetric X,
  with the SUFFICIENT per-diagonal condition "x^s ∈ M(lam^s)": in the order of decreasing lam^s, x^s non-increasing
  AND x^s/lam^s non-decreasing  (⇔ 1 <= x_k/x_{k+1} <= lam_k/lam_{k+1}: log-gaps of x between 0 and those of lam).
  Feasible for ALL 840 thermal instances d=4..12 (incl. p_min/p_max=1e-6), row err <= 1e-10, maj viol <= 2e-11.
  (First run with bad scaling showed spurious infeasibility; rescaled y = X/c_s fixes it.)
  Note: rows target q ∈ M(p) (same log-gap condition). "M-structure": per LC set, final diagonal in M(weights).
- Exp3 (mvert.py): vertices q_S of M(p) are mostly NOT in the M-cyclic set (43/96 fail at d=4, 558/768 at d=7):
  the thermal curve is special (uniform gap scaling), a proof must use the thermal form, not just q ∈ M(p).
- Exp4/5 (profiles.py, profiles2.py, commonG.py): sub-families of M-cyclic: power profiles (lam^tau) fail; concave
  profiles g_s(lam) (= cone of min(lam,m)) almost universal (fails at 3 extreme spectra; genuine); common concave G +
  per-diagonal constant fails ~60%.
- KEY OBSERVATION: M-condition ⇔ log x = F(log lam) with F non-decreasing and 1-Lipschitz on the diagonal's points.
  For thermal q: q_i q_j = (p_i p_j)^t / Z_t^2 is such a function (F = t·id + const) on EVERY LC set. Only the per-set
  sums are wrong.
- NEW sufficient majorisation condition ("threshold box"): if every cell c of an LC set moves from lam_c TOWARD a
  common level m without crossing it (x_c between lam_c and m) and sums are equal, then x ≺ lam (donors stay above m,
  receivers below m; prefix-sum argument). q⊗q satisfies this for EVERY set with the SAME m = θ* := Z_t^{-2/(1-t)}
  (the fixed point θ^t/Z_t^2 = θ). ⇒ Box problem: symmetric Y = X - q⊗q, zero row sums, cyclic-diagonal sums
  Δ_s = c_s(p) - c_s(q), entries in boxes [a_c, b_c] ∋ 0 (a Hoffman-type circulation problem).
- Exp6/7 (box.py, box2.py): "no-overtaking" family. Common threshold theta*: fails at small t. Global split at theta*
  with free per-diagonal thresholds m_s: fails ~10-20%, mostly t≈0 (split should be per diagonal).
- LEMMA (no-overtaking, proved): in an LC set, if every cell that decreased (x_c < lam_c) ends >= every cell that
  increased (x_c > lam_c), and sums agree, then x ≺ lam. (Check Σ(x-a)^+ <= Σ(lam-a)^+ for a above/below a separator.)
- Exp8 (order_test.py): the d=12 loop+common-circulant counterexample becomes FEASIBLE for many non-sorted cyclic
  orders (e.g. tiny level placed right after the top level). Order is a useful extra freedom (no rule found).
- OBSERVATION: X0 = pp^T + diag(q - p) has rows q and ALL cyclic-class sums right; only the loop x0 = p^2 + q - p
  must be majorised by p^2. Also: σ2·thermal(p,τ) ≺ p^2 for all τ ≤ 2 (σ2 = Σp^2; Gibbs-majorisation), in
  particular x0 = σ2 q^2/Σq^2 (loop ∝ q∘q) is always admissible ⇒ reduces to an OFF-DIAGONAL problem:
  off-diagonal cells must reach rows q - k q∘q, k = Σp^2/Σq^2.
- Exp9 (offdiag.py): fixing the loop at x0 = k q∘q (k = Σp²/Σq²) and asking the off-diagonal classes for rows q - k q²:
  infeasible often (target even negative). Dead end.
- Exp10/11 (matchT.py, matchT2.py): loop (general) + per off-diagonal class {partial averaging u_s + T-transforms on the
  "reversal" matching of positions (k-th heaviest with k-th lightest), v <= (1-u)cap}: 0 failures d<=8, but 2-4% fail
  at d=10,12. (Zero-capacity tie pairs must be skipped -> first run had a spurious-failure bug.)
- Exp12 (commonGmult.py): common log-1-Lipschitz G + per-class multipliers (M-condition automatic for any multipliers):
  least squares does not reach zero in 15-40% of cases. Dead end.
- VALIDATION (mcyc_validate.py): M-cyclic construction = LP (interior-margin objective) + per-diagonal rescaling to exact
  sums (scaling preserves the M-condition) + exact loop x0 = q - offdiag rows + Chan-Li rotations.
  Quick runs: marginal errors ~7e-16, spectrum ~4e-16. One tie-degenerate instance (5 equal tiny levels, t=0.99):
  LP numerically infeasible but the loop-only point pp^T + diag(q-p) is valid there (fallback added).
  NOTE: my first patch of mcyc_validate.py via python open() crashed on a non-cp1252 char and TRUNCATED the file;
  rewritten with the Write tool. Background runs seeds 11-14 (500 instances each, d<=12) -> val_*.log.
- VALIDATION RESULT (val_11..14.log): 2000 instances, d=3..12, p_min/p_max >= 1e-6 (6 spectrum families), t in
  {1e-4, 1e-2, 0.5, 0.99, 0.9999, U(0,1)}: 0 failures (1 instance via the loop-only point); worst |spec(rho)-spec(p⊗p)|
  6.7e-16, worst |rho_A - diag q|, |rho_B - diag q| 1.7e-15 (full marginal matrices), every LC diagonal majorised to
  8e-16 (rel.), loop to 4e-15 (rel.).  (M-ratio condition itself only to 3e-4 after polishing: irrelevant, the
  exact requirement is majorisation.)
- dbg7.py: points 0.98 q_S + 0.02 q_{1/2} near M(p)-vertices (d=5): 19/60 NOT in M-cyclic, 0/60 outside full R_cyc.
  => the M-cyclic set contains the thermal curve but not M(p): a proof must use uniform gap scaling.

## STATUS (end of session, ~2h45m)
PROVEN (elementary, all d):
 L1 no-overtaking criterion (decreased cells end >= increased cells, equal sums => majorised).
 L2 log-Lipschitz/MLR criterion (1 <= x_k/x_{k+1} <= lam_k/lam_{k+1} in lam-order) => hypothesis of L1 => majorised.
 L3 for thermal q, q⊗q = φ(p⊗p), φ(λ)=λ^t/Z_t^2, satisfies L1/L2 on EVERY LC set (threshold θ* = Z_t^{-2/(1-t)});
    the only obstruction to X = q⊗q is the LC-set sums.
 L4 loop-only construction X = pp^T + diag(q-p): rows/cols q and all cyclic class sums automatically right; valid iff
    p^2 + q - p ≺ p^2 (always for t in [t0(p),1]).
 L5 (Σp^2)·thermal(p,τ) ≺ p^2 for τ <= 2.
CONJECTURE (M-cyclic, strong numerics, stronger than C1): symmetric X, rows q_t, each cyclic diagonal with its
 weight sum and the L2 ratio condition.   NOT PROVEN for all d.
NEGATIVE: M(p) ⊄ M-cyclic; power/common-G/qpc/concave/matching/monotone-tri/anti-cyclic/fixed-loop sub-families fail.
