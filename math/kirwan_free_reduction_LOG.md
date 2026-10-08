# P-STU3 research log  (elementary all-d proof of C2: M(p) ⊂ R_tri)

## 2026-09-28 session start
- Read stu/REPORT.md, stu2/LOG.md, lcs.py, thermal_construction.py, certs.
- Setup: symmetric WLOG (average X and X^T, same structure). Unknowns: run vectors x^s (s=0 loop, length d-s),
  row i = x^0_i + sum_{s>=1} ([i<=d-1-s] x^s_i + [i>=s] x^s_{i-s}); constraint x^s ≺ λ^s, λ^s_i = p_i p_{i+s}
  (λ^s is non-increasing along the run).
- E1: sorted-run relaxation (each run stays non-increasing) FAILS often (even d=3 uniform) -> runs must be partly reversed.
- E3: top-level induction (hook = first cells of runs donates, IH = M(p') ⊂ R_tri(p')) fails: sub-grid rows must leave M(p').
- E4: loop free + each run in conv{nat, rev, avg} (per run): fails for some vertices from d=5 on (not universal).
- E6: uniform target, "all off-diagonal runs averaged, loop absorbs": fails ~3-14% (loop would need values > p_0^2).
- **E7 KEY: thermal curve ⊂ conv{w_0..w_{d-1}}, w_k = min(p,p_k)/Z_k (top k+1 levels CLIPPED to p_k)** 0 failures.
  PROOF (Lemma T, elementary): sum_k nu_k min(p_i,p_k) = p_i N_i + sum_{k>=i} nu_k p_k with N_i = sum_{k<i} nu_k;
  differences give N_{i+1} = (g(p_i)-g(p_{i+1}))/(p_i-p_{i+1}) (secant slopes of g(x)=x^t), N_d = g(p_{d-1})/p_{d-1};
  g concave increasing with g(0)=0 => secant slopes increase as the interval moves left => nu_i = N_{i+1}-N_i >= 0.
  So ANY concave increasing g with g(0)>=0 gives g(p)/Z in conv{w_k}.  Replaces Lemma 5 (v_k chain).
  => Only need the d chain points w_k in ONE common structure (M(p) not needed).
- **E9 KEY (layer/superposition idea)**: SUPERPOSITION LEMMA: lam = sum_m lam^(m), all lam^(m) non-increasing along the
  run (similarly ordered), x^(m) ≺ lam^(m) => sum x^(m) ≺ lam (top-k sums are subadditive, additive for sorted).
  Layer-cake: p⊗p = ∫ 1_{Y_θ} dθ, Y_θ={p_i p_j>=θ} symmetric Young diagrams (down-sets); on each run an initial
  segment; for a 0/1 run, x ≺ (1^n,0^m) iff x ∈ [0,1], same sum.
  RESULT: EVERY symmetric Young diagram in the d×d box can be spread (runs in [0,1], run sums fixed) to UNIFORM
  rows |Y|/d: all 2^d diagrams, d=3..9, 0 failures.  => u ∈ R_tri (modulo explicit uniformization lemma).
- E10: scheme "B⊗B natural + D-layers uniformised on top intervals" (Hall) fails ~5% -> too rigid.
- E11: uniformisation margins: all symmetric Young diagrams have positive margin (min ~2.4/d^2, tightest: full hook
  (d,1,..,1) and square [0,d-2]^2 which are complement-rotation duals).
- E12: non-symmetric rectangle expansion fails (diagonal moves couple rows and cols) -> discard.
- **KEY IDEA (reweighting)**: q_t⊗q_t ∝ (p⊗p)^t has the SAME super-level sets Y_θ as p⊗p. So
  q_t = ∫ λ(Y_θ) dφ_t(θ)/Σ_t^2... (λ(Y) = row-length vector).  Need: (i) INFLATION LEMMA: layer Y can be spread to
  rows ∝ λ(Y') for Y' ⊇ Y (nested layers); (ii) downward transport of layer mass ν_1=|Y_θ|dθ -> ν_t=|Y_θ|dg(θ).
  (ii) PROVEN: h(θ) = Σ_{x_a>=θ}[(x_a-θ)-(g(x_a)-g(θ))], h(0)=h(∞)=0, h' = |A_θ|(g'(θ)-1), g' decreasing
  => h unimodal >= 0 => ν_1 dominates ν_t from above => downward transport exists (any concave g, g(0)=0).
- E13/E15: per-pair INFLATION (layer Y -> rows ∝ λ(Y'), Y ⊂ Y') fails for ~20% (R_tri) / ~4% (R_cyc) of nested pairs
  (capacity in near-full diagrams).  Aggregate still feasible (LP), but per-pair lemma false.
- Observation: for a run with values x_a, y_a = c g(x_a) (g concave incr, g(0)=0, c normalises sum) satisfies y ≺ x
  (y/x decreasing in x + Chebyshev prefix argument + same order).  So "q⊗q with each run rescaled to the p-run-sum"
  is a valid off-diagonal choice.  Test: loop x0 = q ⊙ (1 - C q), C_ij = c_{|i-j|} = σ_{|i-j|}(p)/σ_{|i-j|}(q).
- E16: explicit "rescaled thermal" runs y^s = c_s q_i q_{i+s} (c_s = σ_s(p)/σ_s(q)), loop absorbs: R_tri fails ~5%,
  R_cyc fails only ~2e-4 (tiny violations x0_0 > p_0^2, t≈1, near-degenerate top cluster + small tail). Not a proof.
- Symmetric Young diagrams <-> arm-length sets A ⊆ {0..d-1} (Frobenius hooks): run counts n_s = |A ∩ [s,d-1]|.
  Uniformisation depends only on (n_s).  => HOOK DECOMPOSITION idea: find configs x^(a) (a=0..d-1), x^(a) >= 0 with
  one unit on the loop and one unit on each run s<=a, rows (2a+1)/d, and sum_a x^(a) = ALL-ONES.  Then every A:
  x^A = sum_{a∈A} x^(a) is a valid uniformisation (capacity <= 1 automatic).  d=3: exists (by hand).
- E17: HOOK DECOMPOSITION of the all-ones configuration EXISTS for d=2..15 (LP) => every symmetric Young diagram
  is uniformisable, uniformly (x^A = sum_{a in A} x^(a)).  Equivalent: monotone chain of square uniformisations.
  E18: min-norm solution not a closed form; still need explicit all-d formula.
- LEMMA (M(p) rescaling): for ANY q ∈ M(p), along each tri-run y_i = q_i q_{i+s} is non-increasing and y/λ = r_i r_{i+s}
  non-decreasing => rescaled y ≺ λ^s (Chebyshev prefix argument).  So rescaled-product runs are valid for all q in M(p).
- **E21 BREAKTHROUGH (reduction of w_k to uniformisation)**: p⊗p = B⊗B + D, B=min(p,p_k), e=p-B,
  D = sym(e⊗(p+B)) = Σ_{m<k,M} c_m c_M (1+[M>=k])/2 (Q_m + U_{m,M})  (c_m = p_m - p_{m+1}; Q_m square [0,m]^2;
  U_{m,M} cross [0,m]x[0,M] ∪ transpose); all components symmetric Young diagrams => similarly ordered on runs.
  B⊗B natural (rows Z B); D-components uniformised on [0,M'] boxes, M' >= max(k, extent); target (1-Z^2)B/Z.
  HALL (nested) holds TRIVIALLY: LHS(c) = 2E Z_c - F p_c, RHS(c) = E(1+Z)Z_c/Z, RHS-LHS = E^2 Z_c/Z + F p_c >= 0
  (E = Σ_{i<k}(p_i-p_k) = 1-Z, F = Σ_{i<k}(2i+1)(p_i-p_k), Z_c = Σ_i min(p_i,p_c)).  Numerically 0/709510 fails.
  Even simpler assignment: big crosses U_{m,M} (M>=k) in their OWN box [0,M]; leftover c_M[E^2(M+1)/Z + F] >= 0
  filled by flexible components (extent < k).
  => w_k ∈ R_tri for all k, and thermal ∈ conv{w_k} ⊂ R_tri, MODULO the uniformisation lemma (squares & crosses).
- wk_construction.py: END-TO-END explicit construction (hook decomposition LP per box size n, p-independent) of
  w_k and thermal targets in R_tri.  verify_wk.py: 1021 w_k + 200 thermal (d<=8): 0 failures, row err 1.6e-15,
  majorisation margins >= -1.7e-15.  Big run (3000, d<=12, extreme spectra) in background -> verify_wk_big.log.
- verify_wk.py big run: 21104 w_k + 3000 thermal instances (d<=12, p_min/p_max down to 1e-6): 0 failures,
  row err <= 7.5e-15, majorisation margins >= -4e-15.
- exact_hookdec.py: EXACT rational hook decompositions for n = 1..20 (HiGHS vertex -> exact QQ solve -> exact check
  of every constraint and nonnegativity), files hookdec_n{n}.txt.
- exact_verify_wk.py: EXACT rational end-to-end check (rows == w_k, runs ≺ λ, >=0): 292 instances d<=7: 0 failures;
  big run (400 spectra, d<=12) in background -> exact_verify_big.log.
- exact_verify_big.log: EXACT: 2788 (p,k) instances, d<=12 (random rational spectra incl. ratios 1e-6, ties,
  clusters): 0 failures.  build_states.py: 300 actual states (Chan-Li rotations), d<=10, thermal t~U(0,1):
  spectrum err 5e-16, full marginal err 6.7e-16.
- Reduced form of the Hook Decomposition Lemma: loop column sums are automatic; need only DS matrices M^s
  (s>=1; rows = hooks a>=s, cols = run positions) with every hook's off-diagonal load on every row <= (2a+1)/N.
- ADDITIVITY LEMMA (proved): if a Young diagram Y (extent e) is uniformisable in the n_j-boxes (n_j >= e+1), then in
  the (Σ n_j)-box: put copies (weights n_j/n) of the n_j-uniformisations in consecutive diagonal blocks (diagonal
  translation preserves runs; values <= n_j/n <= 1; run totals Σ(n_j/n) n_s = n_s; rows |Y|/n).  So for each shape
  only box sizes e+1..2e+1 matter.  Squares: n = b trivial (natural), b | n tiling, n >= b^2: uniform translates +
  loop correction.  Still no closed form for general (shape, box).
- Graph form of the Hook Decomposition Lemma: decompose K_N (unit edge weights, edges grouped by |i-j| = s) into
  fractional subgraphs G_1..G_{N-1}, G_a taking exactly one unit from each class s <= a, with max degree
  <= (2a+1)/N (the loop fills the rest; loop DS column sums are automatic).  Tightest: full hook (a = N-1).

## STATUS / SUMMARY (end of session)
PROVEN (elementary, all d): Lemma T (thermal ∈ conv{w_k}); superposition lemma; decomposition p⊗p = B⊗B + D with
D = Σ ω_{m,M}(Q + U); Hall/assignment identity (leftovers c_M[E^2(M+1)/Z + F] >= 0); additivity lemma.
=> THEOREM (conditional, all d): if every n-box (n <= d) admits a hook decomposition, every thermal target (and every
w_k) is an explicit symmetric marginal inside R_tri (Kirwan-free, no Lemma 5, no M(p)).
UNCONDITIONAL for d <= 20: exact rational hook decompositions n = 1..20 (hookdec_n*.txt, exactly verified).
Verification: float 21104 w_k + 3000 thermal (d<=12, extreme); EXACT 2788 (p,k) d<=12; real states (Chan-Li) 300.
OPEN: explicit all-N hook decomposition (p-independent combinatorial lemma).
- exact_verify_hi.log: EXACT (d=13..20): 678 (p,k) instances, 0 failures.  Float hook decomposition feasible also for
  N = 22, 24, 26, 28, 30.  (Stopped my own slow N=35/40 background LP by PID; other processes untouched.)
- Input (P-STU4 lemmas L1-L5, M-cyclic conjecture) noted; our "rescaled product runs ≺ λ for q ∈ M(p)"
  lemma is the same mechanism as their L2/L3.  Our route yields an unconditional proof for d <= 20 and reduces all d
  to the p-independent Hook Decomposition Lemma.
