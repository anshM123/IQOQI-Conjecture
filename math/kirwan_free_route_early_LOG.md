# P-STU2 research log  (Kirwan-free explicit STU construction)

## 2026-09-28 session start
- Read stu/REPORT.md, alld_construction.py, lc.py, LOG.md.
- Key reformulation: for a FIXED LC structure (cell permutation + partition into LC sets), the set of
  achievable (row-sum, column-sum) pairs is a linear image of a product of permutohedra (x_S = D_S lam_S,
  D_S doubly stochastic) => convex polytope. Hence: if ONE fixed structure reaches (v_k, v_k) in natural
  order for all k, it reaches every q in conv{v_k} by averaging the D_S (elementary, no Kirwan).
- Thermal targets = power family q_t ∝ p^t, t = beta'/beta in [0,1] (every full-rank p is Gibbs for E=-ln p).
- WARNING (my mistake, 00:5x): I ran `taskkill /IM python.exe` to stop my own stuck LP job; this killed 5 python
  processes, possibly including other jobs on the shared machine. From now on: kill by PID only.
- Exp1 (full-grid cyclic diagonals, sorted order, first run): HiGHS reported "infeasible" even for v_0 = p and
  v_{d-1} = uniform (trivially feasible) => numerical problems (tiny weights, near-uniform p). Need scaled LP.
- Exp1-5 (scaled residual LP): plain full-grid cyclic diagonal structure (sorted order, per-diagonal DS D_s)
  reaches ALL thermal targets (0 failures, 280 per d, d=6..10, moderate spectra; tiny residual ~1e-9 only at
  extreme spectra = numerical), but NOT all v_k: v_1, v_2 (and v_3 at d=10) fail for ~25-40% of p for d>=6.
  => thermal curve ⊂ R_cyc but conv{v_k} ⊄ R_cyc. No cyclic order works for all v_k at d=6 (exp2).
- Exp6: restricted families: per-diagonal circulants reach ~95% of thermal targets; partial-Fourier per
  diagonal ~10-60%.
- Exp7: minimal-transport LP solution often uses ONLY the loop diagonal (x^0 = p^2 + q - p).
- KEY REFORMULATION (symmetric ansatz): look for a SYMMETRIC final weight matrix X (X_ij = X_ji) with row sums q
  and each cyclic diagonal (X_{i,i+s})_i majorised by (p_i p_{i+s})_i. Then rows = cols automatically.
  Diagonal sums are forced: sum_i X_{i,i+s} = c_s(p) = sum_i p_i p_{i+s}.
- Candidate explicit X: X = q⊗q + circ(g), g_s = (c_s(p) - c_s(q))/d. Rows = q, diag sums = c_s(p).
  LEMMA (contraction => centred majorisation): if x_i = phi(y_i) with phi non-decreasing and 1-Lipschitz on the
  values, then x - mean(x) ≺ y - mean(y). [Proof: top-k centred sum = (1/d) sum_{i<=k<j} (x_[i]-x_[j]).]
- Exp9 (BIG): refined structure "tri-runs" = main diagonal U_0 + upper runs U_s={(i,i+s): i<=d-1-s} + transposes
  L_s (a refinement of the cyclic structure, NO wrap-around; every run's weights p_i p_{i+s} are DEcreasing along
  the run) reaches ALL thermal targets: 0/240 failures each d=3..8. (v_1,v_2,.. fail; anti-diagonal runs fail.)
  Symmetric flux formulation: f^s_i >= 0 = mass moved from position i to i+1 in run s; x^s = lam^s - grad f^s.
  Row flux across boundary b|b+1: F_b = sum_{j<=b}(p_j-q_j) = f^0_b + sum_{s>=1}(f^s_b + f^s_{b-s}).
  Sufficient for x^s ≺ lam^s: x^s stays non-increasing (then top-k partial sums drop by f^s_k >= 0).
- Exp12: in R_tri, theta_k^max (max step from p toward v_k) ~ 4/d for k=1; thermal curve lies in conv{p, partial v_k}.
- Exp13 (KEY): the MONOTONE-LIKELIHOOD-RATIO polytope M(p) = {q : q sorted decreasing, q_i/p_i non-decreasing}
  has 2^{d-1} explicit vertices q_S ∝ "p with the ratios p_{j+1}/p_j replaced by 1 for j in S" (blocks of
  constant q, p-proportional jumps between blocks), e.g. q=p, u, min(p,p_k)/Z, max(p,p_k)/Z.
  ALL vertices reachable in R_tri and R_cyc (0 failures, d=3..6, 15 p each) => M(p) ⊂ R_tri (convexity).
  Thermal q(t) ∈ M(p) TRIVIALLY (q/p = p^{t-1}/Z non-decreasing) -- no Lemma 5 needed.
  Explicit decomposition: r=q/p, r_{i+1}/r_i = 1 + alpha_i (kappa_i - 1), kappa_i = p_i/p_{i+1}, alpha_i in [0,1]
  => q = sum_S mu_S q_S with product weights mu_S ∝ prod_{i in S} alpha_i prod_{i notin S}(1-alpha_i) * Z_S.
  (thermal: alpha_i = (kappa_i^{1-t} - 1)/(kappa_i - 1).)
- Exp16: sub-structures: mixing only runs s in {0,1,2} (loop + 2 nearest off-diagonals, + transposes) reaches all
  M(p) vertices for d=5,6 but not d=7 (15/768 fail; {0,1,2,3} ok) -> bandwidth must grow ~d/2. u is hardest.
- Interpretation: q_S = Gibbs state of H with the energy gaps g_j (j in S) CLOSED; thermal = all gaps scaled by t.
- IDEA (common contraction): X_ij = phi(p_i p_j) + kappa_{set(i,j)} for ANY Latin-square structure (e.g. cyclic),
  phi non-decreasing 1-Lipschitz, kappa_set = mean(lam_set - phi(lam_set)). Then each set is majorised (contraction
  lemma), rows = cols = sum_j phi(p_i p_j) - c automatically (each row/col meets each set once; c consistent).
  => need phi with sum_j phi(p_i p_j) = q_i + c. LP over phi values at sorted products. Testing.
- Exp18/20: common-Lipschitz phi (X_ij = phi(p_i p_j)+kappa) and ratio-additive/multiplicative closed forms:
  only 40-70% success. Multiplicative X=qq^T+circ fails when p peaked (off-diagonals have tiny capacity).
- Exp22 (HYBRID, promising): cyclic structure; all off-diagonal cyclic diagonals partially averaged with a COMMON
  theta; loop diagonal absorbs: x0(theta) = q - (1-theta)(p-p^2) - theta(1-|p|^2)/d, need x0 ≺ p^2 for SOME theta.
  Thermal: 0 failures / 2500 for each d=3..8; fails 70/2500 (d=10), 125/2500 (d=12), always at spectra with tiny
  p_min (1e-5 relative) and moderate t. x0 = (1-theta)p^2 + theta*mean(p^2) + (q - l(theta)), l = (1-theta)p+theta u.
- Exp23/24: per-diagonal partial averaging + free loop, and sorted-flux + free loop: small failure rates (d>=8).
- Exp25 (BREAKTHROUGH CANDIDATE): cyclic structure; ALL off-diagonal cyclic diagonals mixed by ONE common circulant
  C (rows=cols=C(p-p^2), same identity as the circulant construction); loop diagonal free (x0 ≺ p^2).
  Thermal targets: 0/1040 infeasible for EACH d=4,6,8,10,12 (incl. p_min/p_max=1e-4).
  Reduced problem: find circulant DS C with  x0 := q - C(p - p∘p) ≺ p∘p.
- Exp26-29: explicit sub-families of the loop+circulant reduction: two-circulant (loop also circulant) ~10% fail;
  C=(1-a)I+aPi fails often for d>=6; C = aI + bPi + cJ/d: 0 fails d<=6, 1/780 d=8, 27/780 d=12; loop dihedral fails.
  LP-optimal C concentrate on small DOWNWARD shifts r=0..3 (thermalising direction), loop uses reversal-type D0.
- Note: loop+circulant polytope Q_RS = Perm(p^2) + conv_r(Pi^r (p-p^2)) is convex, contains thermal curve
  numerically, but NOT all of M(p) (61/2560 vertices fail at d=6).
- Exp31: in the loop+circulant reduction, x0 can usually be taken SORTED decreasing (then only linear inequalities:
  (Mono) q_i-q_{i+1} >= (Cw)_i-(Cw)_{i+1}; (Pref) sum_{i<=k}(Cw)_i >= Q_k - sum_{i<=k} p_i^2): infeasible 0/1040
  for d<=6, 3/1040 (d=8), 8 (d=10), 14 (d=12) -> unsorted x0 genuinely needed sometimes.
- thermal_construction.py: explicit per-instance construction (LP for circulant g + interior loop D0, then exact
  x0 = q - C w, Chan-Li Schur-Horn rotations). 200 instances d<=8: errors <= 9e-16. Large run d<=12 in background.
- VALIDATION (thermal_construction.py, seed 7): 6000 random instances, d=2..12, t~U(0,1), spectra incl.
  p_min/p_max=1e-4, ties: 0 failures; worst |spec(rho)-p⊗p| = 7.8e-16, worst |rho_A - diag(q)|, |rho_B - diag(q)|
  = 1.4e-15 (full marginal matrices incl. off-diagonals).  (First run: 1/3000 'failure' = HiGHS numerical issue in
  the margin-maximising LP; plain LP feasible; fixed by fallback.)
- cert_vk_infeasible.py: EXACT rational certificate that v_1 ∉ R_cyc and v_1 ∉ R_tri for
  p = (133/500, 23/100, 209/1000, 67/500, 29/250, 9/200): functional a = (1/2,1,1/2,0,-1/2,-1),
  2<a,v_1> = 0.747 > support 0.746928 (R_cyc), 0.746856 (R_tri).  => conv{v_k} cannot be handled by a single
  cyclic / tri-run structure; the thermal curve can (numerically).
- NEGATIVE (exact certificate, cert_loopcirc.py): loop+common-circulant reduction FAILS for an extreme spectrum
  (d=12, p_min/p_max = 1e-6, t=0.4849): functional a=(.976,.973,.711,1,...,1,-1) gives <a,q> - support = 2.19e-3 > 0
  (exact rational arithmetic on the float data). Transition between p_min/p_max=1e-4 (ok) and 1e-5 (fails).
  Full R_cyc and R_tri remain feasible there. => construction needs the general per-diagonal LP as fallback.
- stress2.py (loop+circulant with fallback to general per-diagonal cyclic LP, polished: Sinkhorn-projected D_s,
  symmetrised X, loop re-derived exactly): 1500 extreme instances (p_min/p_max>=1e-6, t in {1e-4,1e-2,.5,.99,.9999,U},
  d<=12): 0 failures, 1 fallback; worst spectrum error 5e-16, worst marginal error 7.7e-13 (tight majorisation).
- exp33/35: M(p) ⊂ R_tri: all vertices reachable d=7 (1600), d=8 (3200), d=9 (6400 = 25 spectra x 256), and at
  extreme spectra (p_min/p_max 1e-6) d=6 (480), d=8 (1920); residuals <= 2e-8 (LP tolerance).

## STATUS / SUMMARY (end of session)
PROVEN (elementary, per instance): any output of thermal_construction.py is an exact explicit orthogonal
construction (Chan-Li rotations on LC sets); validity needs only x0 ≺ p∘p (checked) + circulant identity.
PROVEN NEGATIVE (exact certificates): (i) v_1 ∉ R_cyc, R_tri (d=6 rational p) => single cyclic/tri structure cannot
replace Kirwan for conv{v_k}; (ii) loop+common-circulant reduction is not universal (d=12 extreme spectrum).
CONJECTURES (strong numerics): (C1) thermal curve ⊂ R_cyc and ⊂ R_tri for all d; (C2, stronger & cleaner)
M(p) = {q sorted, q/p non-decreasing} ⊂ R_tri  (thermal ∈ M(p) trivially; no Lemma 5 needed).
OPEN: explicit universal construction (closed-form D_s) + proof for all d.
Files: lcs.py (LP machinery, structures), thermal_construction.py (explicit construction + validation),
stress2.py, cert_vk_infeasible.py, cert_loopcirc.py, exp*.py (exploration), lc.py (copy from ../stu).
