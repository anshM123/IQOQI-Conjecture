# Experiment log (R-records)

Environment: Windows 11, `.venv` Python 3.12, cvxpy (SCS), numpy; RTX 5070 Ti 12 GB; i9-275HX; 32 GB RAM.

## R001 — max CCNR norm over PPT states (IDEA001)
- Hypothesis: max_{rho PPT} ||R(rho)||_1 grows with d; if > k then PPT states with Schmidt number ≥ k+1 are certified by CCNR.
- Method: see-saw (polar of R(rho) ↔ SDP over PPT states), SCS eps 1e-7. Script `programs/schmidt/ccnr_ppt.py`. Seeds 0..; states saved in `results/ccnr_ppt_d{d}_s{s}.npy`.
- Result: d=3: 1.18879 (best of 3); d=4: 1.500000 (3/3 starts); d=5: 1.500000 (2/3); d=6: 1.500001 (1/3; others 1.467, 1.430).
- d=4 optimizer: rho = P/6 (rank 6), rho^Γ = Q/6 (rank 6), marginals maximally mixed, realignment singular values {1/4, (1/12)×15}; Pauli correlation matrix T = O/3 with O ∈ O(15); no continuous local-unitary symmetry.
- Interpretation: clean rational optimum 3/2 with rank-(6,6) extreme structure; d=5,6 values are consistent with embedded d=4 optima (landscape has many local optima). Status: ACTIVE.

## R002 — SU(2)-invariant spin-j⊗spin-j family (IDEA001)
- Hypothesis: the d=4 optimizer is SU(2)-invariant (e.g. (P0+P2)/6).
- Method: exact vertex enumeration of the PPT polytope of SU(2)-invariant states (`su2_family.py`).
- Result: max CCNR within family: d=4 1.1667, d=5 1.1273, d=6 1.1486, d=8 1.1827, d=9 1.2866, d=10 1.4222, d=11 1.3088.
- Interpretation: hypothesis FALSE (1.1667 < 1.5). Family is weak. Status: KILLED (sub-branch).

## R003 — Bell-diagonal (Pauli-diagonal) PPT states, d = 2^m (IDEA001)
- Derivation (validated vs explicit matrices, m=2,3): rho = sum_x p(x) Phi_x; CCNR = 2^-m sum_y |hat p(y)| (symplectic WHT);
  rho^Gamma Bell-diagonal with eigenvalues q = p * kappa, kappa(a,b) = 2^-m (-1)^{a.b}. PPT <=> p>=0, q>=0.
- Bound: PPT => p(x) <= 1/d, hence CCNR <= d ||p||_2 <= sqrt(d) within this class.
- LP see-saw (`bell_diag_lp.py`, 30–60 starts): d=4: 3/2 (support 6, uniform = (16,6,2) Hadamard difference set / bent-function support);
  d=8: 17/10 (support 19; weights 1/10, 1/20 ...); d=16: 9/4 = (3/2)^2 (tensor square; no better optimum found).
- Unrestricted SDP see-saw at d=8 (4 random starts, 12 iters): only 1.4807 -> random starts are weak in high d.
- d=3 unrestricted (12 starts, 40 iters): 1.18908 (close to 2^{1/4}=1.18921; unconfirmed).

## R004 — exact MILP over Bell-diagonal PPT states (IDEA001)
- d=4: global optimum 3/2 proven (HiGHS, dual bound = primal). d=8: 600 s time limit, incumbent 1.5 (worse than LP see-saw 1.7), dual bound 6.40 -> MILP too weak; needs symmetry reduction.
- Interpretation: 3/2 is the exact Bell-diagonal optimum at d=4 and coincides with the best unrestricted value -> conjecture: max CCNR over all PPT states in 4x4 is exactly 3/2.

## R005 — binary-output triangle nonlocality search (IDEA003) — KILLED
- Tool: web inflation LP (12 parties, all expressible sets <= 6 parties, Z2^3 copy symmetry; `networks/triangle_inflation.py`), validated: GHZ and W refuted, local distributions accepted (0.3 s/test).
- Search: qubit sources + binary POVMs, Danskin gradient on the LP margin t* (max t with Q >= t). Seed 0 drove t* from 1e-5 to 5e-10 (boundary), no infeasibility.
- Stopped after S1 found prior art: arXiv:2605.00981 (Don, Bavaresco, Lipka-Bartosik, Gisin, Brunner, Pozas-Kerstjens, May 2026) proves binary-output triangle nonlocality.

## R007 — CHSH_q via NPA (IDEA027) — PAUSED
- Tool `common/npa_fast.py` (direct sparse SCS; validated: CHSH_2 = (2+sqrt2)/4, I3322 level 2 = 0.2509397, level 1+AB = 0.2514709).
- CHSH_3: level 1+AB = level 2 = 0.71823351 (= Bavarian-Shor); level 3 (577x577, 38017 vars, 147 s) = 0.71238602 = exact 1/3 + 2cos(pi/18)/(3 sqrt3) (arXiv:2604.03700).
- Consequence: for q=5 the standard hierarchy needs level 3 (~24k x 24k) -> symmetry-adapted block diagonalisation (group order ~800) required; the 2604.03700 group has this machinery -> high competition, modest significance. Status PAUSED.

## R008 — 21-point weighted 3-design in C^3 (IDEA060 / S5-02) — REDISCOVERY, KILLED
- Found: Hesse SIC (9) ∪ complete MUB set (12), weights 2/45 and 1/20, is a weighted complex projective 3-design (frame potential = 1/10;
  exact verification over Q(omega) of sum_j w_j P_j^{(x)3} = P_sym/10: 0/729 mismatches; t=4 fails as expected). Script programs/designs/verify_21.py.
- Novelty check: KNOWN. Mohammadpour & Waldron, arXiv:1912.07151 (2019), Example 5.2 and Table (ST25, orbits 9 and 12 -> 21-point (3,3)-design for C^3).
  The scout's "best known 22 numerical / 36 explicit" was outdated. Lesson: verify scout 'records' against the newest paper of the same group.
- Remaining open (low value): minimal size 19–21? (non-existence question); explicit equal-weight 27-point design.

## R010 — P-GYNI: MC1 relaxation (agent; interim) — LEAD
- New relaxation MC1 = moment matrix of W on Lueders word vectors (words {1,A0,A1,A0A1,A1A0} x setting register, Gamma 100x100)
  + free-algebra process-validity constraints + Liu–Chiribella single-trigger canonical processes as linear images of Gamma.
- GYNI: MC1 primal 0.64348483 / dual 0.64348807 (Clarabel AlmostSolved)  vs  Liu–Chiribella 0.759190 (reproduced) and seesaw lower bound 0.6219.
- Sanity: LGYNI MC1 = 0.81940038 (exact 0.819401); random single-trigger functionals reproduce exact LC values within 5e-6; random genuine Lueders strategies satisfy all constraints to 1e-15.
- Coordinator review: WLOG reduction (instrument = X-controlled post-processing ∘ Lueders ∘ fixed isometric pre-processing; absorbed into W) and free-algebra validity constraints look sound. PENDING: general-instrument feasibility test, OCB check, rational dual certificate, MC2 tightening.

## R011 — P-DETEFF — KILLED (rediscovery)
- lambda=1 (double no-click kept): m=3 optimum sqrt(2/3)=0.81650 certified (integer functional, local bound 3) — but already in Massar, Pironio, Roland, Gisin quant-ph/0205130 Table I (2002). m=4: nothing below sqrt(2/3) in 2325 runs.

## R012 — P-REAL (agent; interim)
- Theorem-3 relaxation reproduced: level (2,2) = 7.660479 (symmetry order 192, Clarabel, 30 s). Best real strategy T = 4 sqrt3 = 6.928203 (trine Alice settings, real Clifford Charlie). Gap [6.9282, 7.6605].

## R013 — P-CLOCK (agent; interim)
- Exact reformulation: rank-one clock <=> p = |g|^2, g in span{e^{lambda_k t}}; N*(d) table d=2..64 (d=2: 4.977562 = paper). N/d^2: 1.24 -> 3.27 (d=64); local exponent 2.32 -> 2.17.
- Related: Battagliola & Peralta arXiv:2609.14612 (Sep 2026) least-variable harmonic ME distributions (equal-decay subclass).

## R009/R014 — Tavakoli–Morelli Conjecture 3 (IDEA049) — own
- R009: max over Schmidt-rank-r pure states of ||Q_m||_tr equals 1+(m-1)r/d (tight) for d=3, all m<=3, r<=2 (64 restarts, Adam).
- Reformulation: Q = V^dag (X (x) conj X) V, V columns |e^k_a conj(e^k_a)>, V V^dag = (m-1)Phi+ + P (P projector, rank 1+m(d-1)),
  hence ||Q_m||_1 = ||F (X (x) conj X) F||_1 with F = P + (sqrt m - 1) Phi+.  Tr Q <= 1+(m-1)r/d is the easy "fidelity" version.
- R014 STRENGTHENED inequality (implies Conj. 3 by convexity since Schmidt rank r => ||X||_1^2 <= r):
      ||Q_m(X)||_1 <= ||X||_F^2 + (m-1) ||X||_1^2 / d   for all X.
  Adversarial Adam maximisation of the violation (128 restarts x 2000 steps): max violation <= 4e-14 for d=3 (m=2,3,4) and d=5 (m=2..6). Holds numerically, with equality attained.

## R016 — P-GYNI: CERTIFIED bound (agent; 2026-09-27 ~23:40)
- Containment with GENERAL instruments (random valid W incl. OCB process, d=2,3; non-projective non-Lueders 2-outcome instruments): 15/15 feasible (|p_MC - p| <= 1.7e-9).
- Seesaw d=2 reproduces Boghiu–Simonov 0.5694.
- EXACT CERTIFICATE (certify.py; cert_mc1_gyni.pkl): eps-margin dual, rational rounding, exact rational LDL: 4 Gamma-dual blocks 25x25 PD, 16 image-dual blocks 16x16 PD
  ==> I_GYNI <= 0.6434936237 (exact rational), valid in every dimension. [Liu–Chiribella 2024: 0.7592; lower bound 0.6219]
- Ablation: Gamma PSD + free-algebra validity alone gives the full value; LC canonical images are implied. Hierarchy: L=1 0.7462629 (< LC), L=2 0.6434843, L=3 running.

## R017 — P-QRAC (agent; interim)
- Quaternionic qutrit strategy (complex dim 6 with antiunitary J, J^2=-1): P = 0.6982542781 > P_MUB = 0.6971462 -> any relaxation valid for quaternionic QM (tracial / NV-type) cannot certify MUB optimality; explains the FMT plateau 0.69853.
- Partial theorem T1 conditional on Lemma L (numerically 2045/2048): if two of the three measurements are MU bases, no third POVM beats P_MUB.

## R018 — completed program reports (saved)
- P-TM: Tavakoli–Morelli Conj. 2 & 3 PROVEN (programs/tm/REPORT.md); coordinator re-verified (R015).
- P-STU: STU conjecture proven for d = 5, 6, 7 (exact certificates re-run by coordinator: ALL CERTIFIED; explicit unitaries max marginal error 2e-9; v1 all d).
- P-CLOCK: rank-one clock <=> p=|g|^2 reformulation; N*(d) to d=256 (3.71 d^2); proved N <= 4d^2(1+o(1)) for coherent clocks; prefactor 4.
- P-DIAMOND: alpha* <= 0.70558 < 1/sqrt2 (proved, unreviewed); sharp cot(pi/2d)/d for unitary, Pauli, Schur (d<=3) channels.
- P-REAL: exact real strategy 4 sqrt3; App. H hierarchy floor 2+4 sqrt2 = 7.6569 at every level (explicit model); conjecture T_RQT = 4 sqrt3.

## R019 — P-QRAC final (agent) — PAUSED (open)
- Global search: 511/512 POVM restarts reach P_MUB, none exceed (7e-16). Line inequality (coordinator hint) FALSE (all-computational-basis strategy gives line sums 7, 9 > 6.2743).
- Quaternionic qutrit strategy (dim 6, rank-2 projectors, antiunitary J^2=-1): P = 0.698254278074 > P_MUB (rigorous by construction, rank2_object.npy).
  Degree-7 trace identities are the first to separate complex from quaternionic (span_test.py); FMT's degree-<=6 relaxation 0.69853 is consistent.
- Conditional T1: two MU bases + any third POVM cannot beat P_MUB, given Lemma L (numerical 2045/2048).

## R020 — P-GYNI hierarchy level 3 (agent; numerical)
- L=3: 0.6267400 (primal) / 0.6267556 (dual), nullity 162, 77 s. Gap to seesaw lower bound 0.6219: 0.0048 (LC gap was 0.137). Certificate at L=3 pending.

## R021 — STU conjecture PROVEN FOR ALL d (P-STU all-d circulant construction; coordinator-verified)
- Theorem: for every d, every H_A = H_B, every beta > 0 and beta' in [0, beta], there is a unitary U with both marginals of U(tau_beta (x) tau_beta)U^dag equal to tau_beta'
  (conjecture of Bakhshinezhad, Clivaz, Vitagliano, Erker, Rezakhani, Huber, Friis, J. Phys. A 2019, arXiv:1904.07942; open in Clivaz thesis 2020).
- Proof: (1) explicit v_k in S(p (x) p) for all d, k, sorted p: tail relabelling by cyclic shifts r_j = (j-n) mod n (permutation), then on each cyclic diagonal
  D_s = {|i,i+s>} of T x T a Schur–Horn unitary realising B lambda^(s) with the circulant B = sum_r beta_r Pi^r, beta_r = (1/n - W_r)/P; rows/cols of T get
  sum_r (P beta_r + W_r) pi_{i-r} = P/n; beta_r >= 0 by the bin-packing bound W_r <= q_r(1-1/n) + Q/n <= 1/n. (2) Kirwan convexity => S(p (x) p) convex.
  (3) Lemma 5 (paper App. A.X; re-proved) => thermal point in conv{v_k}. (4) local unitaries.
- Coordinator verification (own code verify_alld_coord.py): 20000 random instances d<=15, all k: marginal error <= 3.3e-16, min beta_r = 0.0139 > 0, majorisation holds; Lemma 5 LP 0/3000 failures.
- Novelty: WebSearch (quota restored) + arXiv search: no resolution found; latest statements of the open conjecture are 1904.07942 and Clivaz 2012.04321; 22 citing papers screened by agent.
- Also: construction (C) and exact certificates for d=5,6,7 (R018) remain as independent confirmation; the strong form "every q majorised by p is reachable" is FALSE for d>=4 (counterexample, P-STU).

## R022 — P-LEAN: Tavakoli–Morelli Conjecture 3 MACHINE-CHECKED (Lean 4 v4.33.1 + Mathlib)
- File formal-conjectures/TMProof/TM.lean (SHA256 B1B87A9EF0FF7084486650450CD7396255FAE92D3CC36E041FABEEA5C0563A7D); `lake env lean TMProof/TM.lean` exit 0 (coordinator re-run, 37 s);
  0 occurrences of sorry/admit/axiom/native_decide; #print axioms: [propext, Classical.choice, Quot.sound] for schmidt_mub_bound, schmidt_mub_bound_mixed,
  tavakoli_morelli_conjecture_3_dual (Tr(O^T Q) form) and tavakoli_morelli_conjecture_3 (traceNorm(probMatrix e f rho) <= 1 + (m-1) r/d, needs m >= 1).
- Also formalised: isGreatest_traceNorm (trace norm = max over orthogonal O of Tr(O^T Q), via SVD from Mathlib spectral theorem), Lemma 1 (orthogonal_weighted_sum_le), Lemma 2 (mub_bessel).
- Scope note: "Schmidt rank <= r" = existence of a Schmidt decomposition with <= r terms (physics definition).

## R023 — P-GYNI final: certificates independently re-verified by coordinator (verify2.py, solver-free exact integer arithmetic)
- L2: 0.643487093345; L3: 0.626793181767; L4: 0.623381680756 = 701865376290605/2^50 (dual blocks PD = True).
- OCB within hierarchy: 0.8535530 (optimal OCB strategy lies inside; tight); LGYNI 0.819401 (tight). Lower bound unchanged 0.6219 (Boghiu–Simonov).

## R024 — P-COOL: new cooling protocols beat swap + thermodynamic length for qudits (answers PRL 134, 070401 open problem)
- Mechanism "m-cycle": machine (d_M = d) with m-1 excited levels tuned around resonance with system transition 0<->k (independently detuned);
  permutation |0,1> -> |k,0> -> |0,2> -> ... -> |0,1>. Per-step dissipation (J^2/2)[1/((m-1)s_k) + (m-1)/s_0] + O(J^3) vs swap (J^2/2)[1/s_k + 1/s_0].
- Coordinator check (verify_mcycle_coord2.py, own code, full density-matrix bookkeeping, I+D identity to 1e-12): s=(.7,.2,.1), k=2:
  3-cycle min Diss/J^2 -> 3.93309 (J=3e-4) vs claimed 3.92857; swap 5.71429 (verified separately) => 31% less dissipation per step.
  (Caveat found: if the two machine excited levels are forced exactly degenerate, the 3-cycle is WORSE: (1/2)(1/s_k + 3/s_0); the detuning is essential.)
- N-step exact protocols (agent): qutrit E=(0,1,2.3), beta=2, lambda=4: N*excess 0.1959 vs swap geodesic 0.2404 (ratio 0.815); low-T ratio -> 1/2; ququarts similar.
- Rigorous lower bound (Reeb–Wolf per collision): excess >= 2 dS^2/((ln^2(d_M-1)+4)N). Optimal constant open.
- Novelty: 17 citing papers of 2404.06649 checked by agent (abstracts); none addresses qudit swap optimality.

## R025 — P-STU2: Kirwan-free route (agent) — partial
- Fixed LC structure => reachable (row,col) set is a polytope (convexity inside one structure is elementary).
- conv{v_k} NOT inside single cyclic structures R_cyc / R_tri at d=6 (exact rational Farkas certificate) -> vertex route needs Kirwan.
- Thermal targets q ∝ p^t lie in monotone-ratio polytope M(p) (vertices q_S = Gibbs with gaps in S closed; explicit product barycentric weights).
- CONJECTURE C2: M(p) ⊂ R_tri (0 failures, 13,600 vertex LPs, d<=9, extreme spectra). C1: thermal curve ⊂ R_cyc (LP-feasible in all tests d<=12).
- Explicit per-instance Kirwan-free constructions (common circulant on off-diagonal cyclic diagonals + loop via Schur–Horn; LP fallback): 7500 instances, 0 failures, errors <= 1e-12.
- Incident: agent ran taskkill /IM python.exe once (may have killed other agents' jobs); agents warned.
- Follow-up: P-STU3 launched to prove C2 for all d.

## R026 — P-LEAN-STU: IQOQI STU conjecture MACHINE-CHECKED (conditional on Kirwan convexity only)
- formal-conjectures/STUProof/{SchurHorn,Construction,Lemma5,STU,Axioms}.lean; coordinator ran check.sh: exit 0 (124 s), no sorry/admit/native_decide/axiom;
  #print axioms = [propext, Classical.choice, Quot.sound] for schurHorn, vk_reachable, lemma5, gibbs_mem_convexHull, symMarginalSpectra_eq(_charpoly),
  stu_of_mem_symMarginalSpectra, stu_exists, stu_exists_all.
- stu_exists (hK : KirwanSymmetricConvexity d) ... : ∃ U unitary, both partial traces of U (τ_β ⊗ τ_β) U† = τ_β' (E sorted, 0 <= β' <= β).
  KirwanSymmetricConvexity d := ∀ w, Convex ℝ (symMarginalSpectra w)  — an instance of Kirwan 1984 (moment map of U(d)×U(d) on a U(d^2) coadjoint orbit).
- Fully proven (unconditional): real Schur–Horn existence; explicit v_k construction (greedy bin-packing variant); Lemma 5 with explicit weights; reduction stu_of_mem_symMarginalSpectra.
- SHA256: STU 7094a6d1..., Construction 43190f49..., SchurHorn 23af758b..., Lemma5 868a2b65..., Axioms ab24c25a....

## R027 — P-CLARISSE (agent) — main conjecture II.1 still open
- Disproved companion Conjecture II.2 (filtered witnesses exact) for k=3, d=4 with a certificate (relative gap ~1e-5; explains missed 2005 numerics).
- Proven lemmas: reformulation, frame lemma beta_max >= k(d-1)/((d-k) b1 b2), tight-set lemma, explicit d=3,k=2 decompositions; 3x3 covering proof of beta=14 partially certified (8/12 rows).

## R028 — P-GYNI follow-up: certified I_GYNI <= 0.622219859 (level 7), coordinator re-verified (verify3.py, solver-free)
- Observable (O_x = 2P-1) formulation, dihedral symmetry, custom Schur-complement IPM (L5 12 s, L7 112 s @ 4.6 GB).
- Certified: L4 0.6233557, L5 0.6224213, L6 0.6222568 (coord. re-check 0.622256812119), L7 0.6222199 (coord. re-check 0.622219859087 = 700557281382181/2^50).
- Lower side: explicit 2-Jordan-angle Lueders strategy, exact rational verification 0.621789802790 (below Boghiu–Simonov 0.6219). Level-6 moment matrix not flat.
- Gap now 3.2e-4 (from 0.137). Extrapolated hierarchy limit 0.62208–0.62218; convergence of the hierarchy unproven.
- Bug caught by agent: LAPACK subset eigensolver inaccurate on a 1638-fold null cluster -> full eigendecomposition + row checks.

## R029 — THEOREM: Clarisse's conjecture II.1 holds for k = 2 on C^3 (x) C^3 (P-CLARISSE; coordinator-verified)
- Statement: for every state rho on C^3 (x) C^3, I + 14 rho has Schmidt number <= 2 (previous best proven 3x3 constant 10, arXiv:2604.02420 Thm 4; optimum in [14,15]).
- Proof: convexity -> pure psi = sum b_i|ii>; filter identity I + beta psi psi* = F(C(x)C + beta Omega Omega*)F^dag (c = 1/b); monotonicity in c (adds product terms) and in beta;
  frame lemma (T(|Phi0>><<Phi0|) = Omega Omega* + (1/4) sum_{i!=j}|ij><ij|, valid for beta <= 4/(b1 b2)); Lemma 3 explicit decomposition under (A),(B)
  (coefficient matching verified by hand by coordinator); exact-rational covering of (b2,b3) in [0,.71]x[0,.58]: 1257 leaves (E=73, I=30, II=1154), tiling exact (36864 sub-boxes).
- Coordinator ran independent checker check3.py (pure Fractions, recomputes L,U from stored r): CHECK PASSED; min(U-14) = 0.0255, min(U-L) = 0.0039.
- Also: Clarisse II.2 is FALSE (k=3,d=4), certificate ii2_rigorous.py (exact rationals + mpmath intervals): CERTIFIED beta_max < W.

## R030 — P-STU4 (agent): Kirwan-free route, partial
- Proven (all d): L1 no-overtaking majorisation criterion; L2 log-Lipschitz (MLR) criterion; L3 thermal structure q_iq_j = phi(p_ip_j) satisfies L1/L2 on every LC set
  (only obstruction to X = q(x)q: LC-set sums); L4 loop-only construction X = pp^T + diag(q-p) is a valid Kirwan-free STU iff p^2 + q - p ≺ p^2 — holds for t in [t0(p), 1];
  L5 Gibbs majorisation lemma.
- Conjecture (M-cyclic): per cyclic diagonal, sum preserved + L2 ratio condition + rows = q_t is LP-feasible for all d,p,t (0/1200 infeasible; 2000 explicit-unitary instances, 0 failures,
  marginal error <= 1.7e-15; solves the d=12 loop+circulant counterexample). M-cyclic does NOT contain all of M(p) (vertices fail) -> proof must use thermal gap scaling.

## R031 — P-STU3: KIRWAN-FREE proof of the IQOQI STU conjecture for all d <= 20; all d modulo one p-independent combinatorial lemma
- Route: Lemma T (thermal q_t = convex combination of clipped points w_k = min(p,p_k)/Z_k; hinge decomposition of concave x^t) + fixed tri-run structure R_tri
  (convexity inside one structure is elementary) + Young-diagram decomposition p(x)p = B(x)B + D + superposition lemma + Hall assignment + Hook Decomposition Lemma (p-independent) + additivity lemma; Chan–Li rotations give explicit orthogonal U.
- Hook Decomposition Lemma: exact rational certificates n = 1..20 (hookdec_n*.txt); coordinator's independent checker coord_check_hook.py: all 20 verified exactly. LP-feasible (float) n = 22..30.
- End-to-end exact verification (agent): 2788 + 678 instances d <= 20, 0 failures; coordinator re-run exact_verify_wk.py: 522 instances d <= 8, 0 failures.
- Next: P-HOOK (prove lemma for all n) and P-LEAN-STU resumed (formalize Kirwan-free route with HookDecomposition hypothesis; instantiate small n).

## R032 — Tavakoli–Morelli Conjecture 2 (EAMs) MACHINE-CHECKED (P-LEAN-TM2; coordinator re-compiled)
- formal-conjectures/TMProof/TM2.lean (SHA256 5e0c40a3...; imports TM.lean, unchanged B1B87A9E...). Compile exit 0 (79 s); no sorry/admit/axiom/native_decide;
  #print axioms standard only for tavakoli_morelli_conjecture_2 (traceNorm(eamProbMatrix) <= (d(d-1)+r(n-d))/(n(n-1)), hyp d < n as in the paper), _dual, eam_bessel,
  schmidt_eam_bound(_mixed), traceNorm forms, eamProbMatrix_eq_trace, sanity example traceNorm_trine_bellState (tight, 2/3).

## R033 — P-PPT (agent): no PPT state with Schmidt number 3 found in 4x4 or 3x4 (both still open) — PAUSED
- TM-bound witnesses (r=2) never violated by PPT states (4x4 m=2..5 maxima 1.293/1.625/2.027/2.500 vs bounds 1.5/2/2.5/3); SU(2)-invariant PPT families all SN<=2;
  random low-birank extreme PPT states SN<=2 numerically; KG 4x5 SN-3 state projected to 4x4 decomposes (SN 2); exact Groebner range-criterion searches: ~55 hits, PPT forces zero weight.

## R034 — P-GYNI interim (agent log, BEFORE coordinator verification): certified interval 0.622164967795 <= I_GYNI <= 0.622212366531
- Lower bound from an explicit 4-Jordan-angle Lueders strategy (A_I = C^8, A_O = C^16 per party), exact PD certification of 91 blocks (Bareiss) -> EXCEEDS Boghiu–Simonov 0.6219.
- Verification by coordinator pending (agent resumed to package a stand-alone verifier).

## R035 — P-OCB (agent) — partial rigidity for the OCB causal game (minor)
- T1 (proved): with ideal qubit instruments trusted, W_OCB is the unique valid qubit process reaching S* = (2+sqrt2)/4; robust ||W - W_OCB||_2 <= 28.6 sqrt(eps) + 17 eps.
- T2 (proved): with W_OCB trusted, optimal instruments pinned up to classical relabellings (Alice: measure Z, output |x>; Bob b'=0 measures Z; encoders |+-_b> -> |y+b>).
- T3: corollary of Liu–Chiribella disk bound: |s_i - 1/sqrt2| <= 2^{3/4} sqrt(eps) + 2 eps; Helstrom-optimal decoding.
- Certified (exact dual, hierarchy of R016): game-relevant per-configuration probabilities within 0.214/0.052/0.015/0.0059 of cos^2(pi/8) at eps = 1e-2..1e-5.
- Novelty: 2606.25124 self-tests the quantum switch via Bell tests (leaves causal-inequality rigidity open) -> do NOT claim "first self-test of ICO".

## R036 — IQOQI STU conjecture MACHINE-CHECKED WITHOUT KIRWAN: unconditional for every d <= 20 (coordinator re-ran check.sh)
- formal-conjectures/STUProof/{KirwanFreeCore,KirwanFreeHook,HookCertificates,KirwanFree}.lean (+ earlier files unchanged). check.sh: 8 files, exit 0, 324 s; no sorry/admit/axiom/native_decide;
  #print axioms standard for all 25 theorems incl. stu_exists_le_20, stu_exists_kirwanFree, stu_exists_of_hookDecomposition, hookDecomposition_le_20, lemmaT, wk_reach, ReachTri.convex.
- stu_exists_le_20 (hd : d <= 20) : ∃ U unitary, both partial traces of U(τ_β ⊗ τ_β)U† = τ_β'  — NO hypotheses (Hook certificates n<=20 checked by `decide +kernel`).
- stu_exists_of_hookDecomposition (hH : ∀ n, HookDecomposition n) : all d — remaining input is the p-independent combinatorial Hook lemma (P-HOOK working).

## R037 — P-HOOK: Doubling Lemma HD(M) => HD(2M) PROVEN (coordinator checked the proof by hand); HD(n) verified exactly for all n <= 40 and even n <= 80
- Construction: Z_c = (1/2)Y_c (+) (1/2)Y_c; Z_{M+c} = (1/2)Y_{M-1-c} (+) (1/2)Y_{M-1-c} + Y_c on the cross block. Runs: blocks cover 0..M-1-c, cross covers M-c..M+c;
  rows (2M-2c-1)/(2M) + (2c+1)/M = (2(M+c)+1)/(2M); cells J/2 + J/2 = J.
- Closed form for n = 2^k (XOR formula). New exact certificates odd n = 21..39. => Kirwan-free STU proof holds for all d <= 40 (paper + certificates); Lean currently d <= 20.
- Open: odd n > 39 (black-box odd recursions LP-infeasible). Follow-up P-HOOK2: shrinking lemma HD(N) => HD(N-1) (would finish all n via powers of 2).

## R038 — GYNI upper bound independently re-verified at level 8 (coordinator re-run)
- verify3.py cert3_L8.pkl (dihedral-symmetric dual certificate, exact rational PD check of all dual blocks): VERIFIED BOUND = 0.622212366531
  (= 700548845513581/1125899906842624), 903.9 s, exit 0 (log gyni/coord_verify_L8.log). Lower-bound strategy certificate (J4) re-check still running.

## R039 — Coordinator re-check of all P-HOOK certificates (independent checker stu3/coord_check_hook.py, own driver hook/coord_check_all.py)
- All 60 files certs/final_n*.txt VERIFIED EXACTLY: n = 1..40 and all even n = 42..80 (log hook/coord_check_all.log). => HD(n) for all n <= 40
  (hence Kirwan-free STU for all d <= 40, on paper + certificates).
- Launched in parallel: P-HOOK2 (shrinking lemma / explicit), P-HOOK3 (odd step with boundary invariant), P-UNIF (weaker per-interval
  uniformisation lemma that suffices for the STU proof), P-LEAN-DBL (Lean: doubling lemma + odd certificates -> d <= 40).
- Coordinator observation: the Lean STU proof uses HD(n) only through per-interval uniformisations unif n x lo hi (symmetric, [0,1], run sums
  #{a in [lo,hi]: a >= s}, rows ((hi+1)^2-lo^2)/n), each interval independently -> a per-interval lemma UNIF(n,lo,hi) suffices.
- Coordinator lemma (product): parity-split decomposition of the K-box (E_g rows (g+1)/K on diagonals t = g mod 2, O_g rows g/K on the others)
  + HD(M) => HD(KM) via Z_{gM+c} = E_g (x) Y_c + O_g (x) Y_{M-1-c}; parity-split objects exist only for even K (K=2 gives doubling).

## R040 — GYNI lower bound independently re-verified (coordinator run of the stand-alone exact verifier)
- verify_strategy.py GYNI_J4_strategy_cert.npz: J=4 (A_I dim 8, A_O dim 16), 1895 terms; realness, process validity (every term pattern-pure with an
  allowed pattern; coordinator re-derived the allowed-pattern rule "A_O => (B_I and not B_O), B_O => (A_I and not A_O)" from normalisation on
  product CPTP maps), Tr W = 256, block structure, exact PD of all 676 integer blocks (Bareiss), exact Lueders instruments; exact value
  I_GYNI = 0.622165901354. RESULT all checks passed (2246 s). Logs gyni/coord_verify_J4.log.
- => 0.622165901354 <= I_GYNI^max <= 0.622212366531 (upper: R038, L8 dual; relies on the hierarchy-validity proof in gyni/LOG.md).
  Width 4.65e-5. Literature before: [0.6219, 0.7592].

## R041 — P-HOOK2: T/H/G two-token ansatz; HD(n) certified for all odd n <= 61 (coordinator re-verified) => STU unconditional for d <= 62
- Two-token construction (hook2/LOG.md): Y_a(i,j) = 1/2 T(|i-j|,a) + 1/2 H(m'(i+j),a), m'(x) = min(x+1, 2n-1-x); on the main antidiagonal
  i+j = n-1 the second term is 1/2 G(|i-j|,a). Row-independence lemma (circular distances in Z_2n); image-kernel lemma (T=H solving
  (n-s)T_s + 2 sum_{t=s+1,s+3,..<=a} T_t = 2 is a valid hook for a <= (n-1)/2); rows <=> E'(r)+E'(n-1-r)+G(|n-1-2r|) const, E'=cumsum(T-H).
  Continuum: this is the discretisation of label = 1-(1-l)W, W ~ 2w (max of two uniforms), l = run level or antidiagonal level w.p. 1/2
  (coordinator checked the continuum run identity (1-s)k(a|s) + int_s^a k(a|t)dt = 2 for k(a|l) = 2(1-a)/(1-l)^2).
- Shrinking/growing with adjacent hook shifts: LP-infeasible when iterated (tower N <= 5/6) -> closed negatively.
- Certificates hook2/certs/thg*_n*.txt: coordinator driver hook2/coord_check_thg.py (independent checker stu3/coord_check_hook.check):
  ALL odd n = 3..61 VERIFIED (n=61: 75857 exact entries, denominators ~1e598). Negative control: a corrupted n=7 file is rejected ('run',3,1).
- => HD(n) for every n <= 62 and every n with odd part <= 61 => Kirwan-free STU unconditional (paper + certificates) for all d <= 62.
- Stopped the coordinator's exact_odd.py 41..49 hedge job (n=41 done in 895 s; superseded).

## R042 — P-HOOK3: WP reduction of the odd step (recursive route); certificates re-verified
- Negative: the oddstep.py near miss cannot be repaired by any input condition (loop at m sums to -(1-g_M(0))(M-1)/(2M+1) < 0 for M >= 2;
  middle-row cells need sum kappa <= 1/2, false for s < (2-sqrt3)M; top-hook refill infeasible from M+1 = 16 even with LP-chosen input).
- New reduction "WP": small hooks = theta-mixture (theta = (M+1)/(2M+1)) of Yp_c (M+1-box) and Y_c (M-box); big hook M+c = Yp_c on the cross
  block + W_c on A* mirrored on B*; everything exact iff W_0..W_M >= 0 solve an LP on the M-box using only Yp's top hook on A* and its last
  column. WP feasible for all inputs tried (LP certs M+1 <= 20, doubled, 42 random vertices, self-generated recursion in float to n = 70).
- Recursive exact pipeline D(1) -> doubling (even) / WP (odd): certificates hook3/certs/rec_n2..32.txt and wp_n41.txt re-verified by the
  coordinator with the independent checker: ALL PASS (n = 2..32, 41).
- Open: "WP(Yp) feasible for every rho-symmetric HD(M+1) decomposition" would give HD(n) for all n (with doubling).

## R043 — Image-kernel range and residuals (coordinator computation, exact Fractions, hook2/imgkernel.py)
- A_max(n) = largest A with image kernels of hooks 0..A all >= 0: 0.667n (n=21), 0.756n (41), 0.787n (61), 0.802n (81), 0.822n (101) — increasing.
- Residual rho(l) = 1 - sum_{a<=A} kappa_a(l): at A = (n-1)/2 min rho >= 0.2 for 6 <= n <= 101 (0.067 at n=5, 0 at n=3); at A = A_max min rho > 0
  (0.027 at n=101), except n = 4, 7 (small, certificate-covered).
- => per-interval UNIF(n, lo, hi) is explicit (sum of image hooks lo..hi, entries in [0,1]) for all hi <= A_max(n) (numerically), provably for
  hi <= (n-1)/2 once rho >= 0 is proved (lemma (d) gives rho(l) >= 0 for l >= 1; l = 0 needs a sharper bound).
- Coordinator self-similarity identity (sent to P-HOOK2): after image-kernel hooks 0..A, every short run s <= A carries residual low-level token
  mass L(s) = (n-A-1) - [A-s even]; product ansatz rho(l)phi(a) makes the upper problem an (n-A-1)-size problem with a collapsed reservoir.

## R044 — Lean: STU unconditional for d <= 40 (P-LEAN-DBL), coordinator re-run PASSED
- New: HookDoubling.lean (hookDecomposition_double via cell form hookDecomposition_iff_cells), HookCertSplit.lean + HookCert21..39.lean
  (split decide +kernel, Elab.async false), KirwanFree40.lean: hookDecomposition_le_40, hookDecomposition_two_pow_mul_le_40, stu_exists_le_40.
- Coordinator's own full run of STUProof/check.sh: CHECK_EXIT=0 after 920 s; all 33 #print axioms = [propext, Classical.choice, Quot.sound];
  no sorry/admit/axiom/native_decide (log: scratchpad/coord_check_stu40.log).

## R045 — P-UNIF: explicit closed-form per-interval uniformisation X(n,lo,hi) (weaker lemma sufficient for STU)
- Renewal squares U^m_n (m <= n-2): K = n-m-1, H(l) = 1 - K^2/((n-l)(n-l+1)); end blocks weight H(l), interior blocks H(l)-H(l+1); reversal
  (antidiagonal) permutations of blocks. PROVED all n: weights >= 0 (H(l)-H(l+1) = 2K^2/((n-l-1)(n-l)(n-l+1))), rows const (flow), runs,
  entries <= 1 (concentric blocks; cell value = alternating sum sum_{l=s+1}^{s+1+2k_B} (-1)^{l-s-1} H(l)). Complement gives UNIF(n,lo,n-1).
- General crosses: X = th U^hi_n + (1-th) avg_t J[W_t] - 1/2 U^{lo-1}_n - 1/2 avg_t U^{lo-1}_b[W_t], b = hi+1, W_t = [t,t+hi], th = 1-lo^2/(2b^2).
  PROVED all n: symmetric, runs, rows, X <= 1, X >= 0 on runs s >= lo. OPEN: X >= 0 on runs s < lo (1 <= lo <= hi <= n-2); verified exactly by
  P-UNIF for n <= 76 (76,076 cases); min margin ~2.1/n^2 at lo = hi = n-2.
- Coordinator independent re-implementation from the formulas only (unif/coord/coord_check_X.py): ALL (lo,hi), n = 1..30 (4,960 cases) VERIFIED
  exactly (symmetry, 0 <= X <= 1, runs, rows).
- => STU for ALL d follows from the single inequality (after refactoring the Lean proof to per-interval uniformisations).

## R046 — P-HOOK2 canonical-delta construction; HD(n) certified for all odd n = 7..101 (coordinator re-verified) => STU unconditional d <= 102
- Delta model (hook2/LOG.md): hooks a <= (n-1)/2 = image kernel (proved valid); hooks (n-1)/2 < a <= n-1-k = "delta-modified image kernel",
  one scalar delta_a per hook (canonical: smallest delta >= 0 making it nonnegative; explicit rational; 0 while image kernel >= 0, a < ~0.78n);
  only the top k(n) hooks are an LP remainder, k = 2..5 for n <= 101 (k ~ log n).
- Certificates certs/delta_n*.txt, odd n = 7..101: coordinator re-verified with the independent checker (58 s total): ALL PASS.
- => HD(n) for all n <= 102 (doubling for even n) => Kirwan-free STU unconditional (paper + exact certificates) for every d <= 102.
- 11:30 resumed P-LEAN-UNIF, P-UNIF (phase 2: X >= 0 on short runs), P-HOOK2 (phase 2: top layer) after the API session limit.

## R047 — P-HOOK2 two-dipole construction (O(n) parameters); certificates odd n = 3..101 re-verified
- Two-dipole hooks: A = floor((n-1)/2); for hook a a dipole vector D on levels (n-1)/2 < t <= a; G(u) = sum_t D(t)[u <= 2t-n-1]; T from the
  image recursion with RHS 2 + 2 sum_{t = s+1 mod 2, t>s} D(t) - [n-s odd]G(s); H = T - D. LEMMA (proved; coordinator re-checked the row
  partition [r>=t] + [r<=n-1-t] + [n-t<=r<=t-1] = 1 for t > (n-1)/2): runs [s<=a] and rows (2a+1)/n hold for EVERY D.
- Construction: hooks a <= A image kernel (D=0); A < a <= n-2: D = c1 e_a + c2 e_{a-1} (c1 >= 0, c1+c2 >= 0); top hook = remainder.
  HD(n) <=> cellwise nonnegativity. Certificates certs/dip2_n*.txt (LP-vertex coefficients, exact): coordinator re-verified ALL odd n = 3..101.
- Findings: pure image kernel first negative at n - a ~ 0.78 n^(2/3); residual parity identity (n-s)rho_T(s) + 2 sum rho_H + [n-s odd]rho_G = 2N'.
- Conjecture (P-HOOK2): the O(n)-variable dipole LP is feasible for every n >= 5 (=> HD(n) for all n).

## R048 — P-UNIF Phase 2: no all-n proof of X >= 0; structural reductions
- Proved: renewal-square cell = Psi(|i-j|+1) + Psi(m'+1), Psi(p) = sum_{l>=p} (-1)^{l-p} H(l) (checked on 206,770 cells) => renewal squares are
  exactly partial sums of image hooks; difference construction U^hi - U^{lo-1} valid iff a 1-D condition C(p) = Psi_P(p+1) - Psi_N(p+1) >= 0 for
  p < lo; fails only for lo > n/2 with K^3 <~ n^2 (K = n-1-hi): parity terms ~1/K^2 vs positive part ~K/n^2.
- Toeplitz+Hankel reduction: per-interval UNIF follows from a 1-D linear system in T,H,G >= 0 (runs, E'-row condition, cells <= 1); LP-feasible
  for all core cases n <= 36 (G = 0 suffices except odd n, lo = hi = n-2).
- Negative: no robust c/n margin near the top (best LP margin for lo = hi = n-2 is ~8.5/n^2): any proof must be exact to second order.
- Next (assigned to P-HOOK2 Phase 3): per-interval sums of two-dipole hooks (runs/rows automatic for any dipole vector) to fix the K^3 <~ n^2 region.

## R049 — Per-interval UNIF via D_ren + two top dipoles (P-HOOK2 Phase 3): coordinator-verified for ALL intervals, every n <= 140
- Construction: D_ren = U^hi - U^(lo-1) (= image family, P-UNIF L7) where valid; otherwise dipoles at levels hi, hi-1 with rational amplitudes
  (hook2/certs/unif_dip_n{n}.txt). Lemmas L1-L6 (runs, row-level multiset, dipole identity, rows, symmetry, 1-D cell reduction) proved for any
  amplitudes. Open: explicit amplitude rule + proof for all n (corrections needed only for K_P <~ 0.74 n^(2/3), lo >~ 0.53n).
- Coordinator independent implementation from the report formulas only (unif/coord/coord_check_dip.py): FULL-matrix exact check (symmetry,
  [0,1], runs, rows, and D=0 => equals renewal difference) of every interval for n = 2..30; exact 1-D level check of every interval for n = 2..140
  (e.g. n=140: 9870 intervals, 209 corrected): ALL PASS.
- => UNIF(n, lo, hi) for all intervals, all n <= 140 => (with the Lean-proved reduction stu_exists_of_intervalUnif) STU for every d <= 140
  (Lean reduction + exact computer certificates checked in Python; Lean-internal unconditional range remains d <= 40).
- Launched P-PROOF (iqoqi/programs/proof): computer-assisted all-n proof of UNIF (D_ren region by exact Psi bounds; near-top by dipoles).

## R050 — Lean: all-d STU reduced to ONE explicit inequality (P-LEAN-UNIF), coordinator re-run PASSED
- New Lean files: IntervalUnif.lean (IsIntervalUnif, IntervalUnifAll, intervalUnifAll_of_hookDecomposition), KirwanFreeU.lean
  (stu_exists_of_intervalUnif), Renewal.lean (isIntervalUnif_renU for all n; boxJ; compl), CrossUnif.lean (crossX, isIntervalUnif_crossX given
  XShortNonneg), KirwanFreeAllD.lean (stu_exists_of_shortNonneg, stu_exists_all_of_shortNonneg), ShortNonnegSmall.lean (xShortNonneg_le_8 by
  kernel computation over Q; stu_exists_le_8_of_unif).
- Coordinator's own full check.sh run: CHECK_EXIT=0 after 1076 s; all 44 #print axioms = [propext, Classical.choice, Quot.sound]; no forbidden
  keywords (scratchpad/coord_check_unif.log). Definitions reviewed by coordinator (IsIntervalUnif, renU two-term form, crossX, XShortNonneg).
