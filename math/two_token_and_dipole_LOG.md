# P-HOOK2 research log (Hook Decomposition Lemma HD(n) for all n)

## 2026-09-28 session start
- Read hook/LOG.md, doubling.py, xor_formula.py, oddstep.py, assemble.py, stu3/coord_check_hook.py, exact_hookdec.py.
- Probabilistic reformulation: HD(n) <=> joint law of (I,J,A), (I,J) iid uniform on [n], A independent of I and of J,
  P(A=a) = (2a+1)/n^2 (= law of max of two uniforms), and A | (J-I=d) uniform on {|d|,...,n-1}.
  (Y_a(i,j) = P(A=a | I=i, J=j).)
- Scope note: P-HOOK3 owns the odd step (direction 3). This work package: (1) shrinking lemma, (2) explicit all-n.
- SHRINK test (shrink_lp.py): keep every cell's mass in its cell, split old hook a between new hooks a and a-1
  (monotone coupling of run laws forces the split totals): INFEASIBLE for XOR solutions N=4,8,16,32 deleting vertex
  N-1, N/2, N/2-1, 0 (except N=4 deleting an inner vertex).  (N=4 by hand: cell (1,2) lies entirely in old hook 3.)
- LAYER VIEW (new): an integral "layer" = for every run s a bijection positions -> hooks {s..n-1}
  (equivalently a chain S_0 c S_1 c ... c S_{n-1} = box of symmetric cell sets, S_a with run content (a+1-s)^+).
  Any mixture of layers satisfies runs+cells exactly; HD(n) <=> uniform row profile (2a+1)/n is a mixture of layer
  degree profiles (reduced form: off-diagonal degree <= (2a+1)/n).
- INTERVAL-GROWTH (IG) layers: S_a = I_a x I_a, I_a an interval grown one endpoint at a time (hook a = star from the
  new vertex + its loop).  Degree profile (a+1)[tau(r)=a] + [tau(r)<a]  =>  a mixture of IG layers solves HD(n) iff
  every vertex's insertion time tau(r) is UNIFORM on {0..n-1}.  Impossible (last vertex is an endpoint); even the
  reduced form fails for n>=4 (top hook).  Top hooks must be path-like (graceful Hamiltonian path + loop), cf. XOR.
- IG+zigzag layer mixtures (layerlp.py): feasible n=3,4 only; infeasible n=5..11.  Rank-based random layers
  (random permutation scores ranked within runs, ranklayer.py) far from uniform.
- CONTINUUM STRUCTURE (new reading of the smooth continuum solution k_b(t)=(1-b)/(1-t)^2 + images):
  label of cell (u,v) = 1-(1-l)W, W ~ density 2w, where the LEVEL l is the run d=|u-v| or the antidiagonal level
  m=min(u+v,2-u-v) with prob 1/2 each.  Magic: per row the level is U[0,1] (-> label density 2b); per run the level
  is (1/2)delta_d + (1/2)U[d,1] (-> label uniform on [d,1]).
  DISCRETE: with the Neumann-shifted level m'=min(i+j+1, 2n-1-i-j) in [1,n], the per-row level distribution is
  row-INDEPENDENT: P(0)=P(n)=1/(2n), P(l)=1/n (1<=l<=n-1).  Row-independence for kernels T (run level), H (m' level):
  iff T(l,a)-H(l,a) is symmetric under l <-> n-l.  Runs: (n-s)T(s,a) + 2 sum_{t=s+1,s+3,..<n} H(t,a) + [n-s odd]H(n,a)
  = 2[a>=s].  With T=H the recursion oscillates in parity and goes negative (n-4 level) -> need T != H / fixes.
- T/H ansatz (thlp.py): Y_a(i,j) = 1/2 T(|i-j|,a) + 1/2 H(m'(i+j),a) for ALL hooks: LP-feasible for even n<=24 and
  odd n<=13, INFEASIBLE for odd n=15..35; with g general top hooks: g=2 ok up to n=31, g=3 needed at 33..41.
- **T/H/G ansatz (thglp.py)**: same but cells on the main antidiagonal i+j=n-1 (level n) get Hankel part
  1/2 G(|i-j|,a) (run-dependent): FEASIBLE for ALL hooks (g=0), odd n = 5..33.  Row condition becomes
  E(r)+E(n-1-r)+G(|n-1-2r|,a) = const, E(k)=sum_{t<=k}(T(t,a)-H(t,a)).  (T=H forces G=delta_{n-1}: infeasible.)
- Pure image kernel (T=H, G=0; recursion (n-s)T_s + 2 sum_{t=s+1,s+3..<=a} T_t = 2) is forced for hooks
  a < (n-3)/3 and stays positive for a < ~0.78n (first negative a: n=21:15, 41:32, 81:66, 161:138).  Fixing hooks
  0..firstneg-1 to it, the T/H/G LP for the rest stays feasible (thg_fiximg.py, n=9..41) -> only the top ~22% of the
  hooks need T != H, G != 0.
- SHRINK tests continued: adjacent-shift shrink also INFEASIBLE for the T/H/G solutions (N=5..15, deleting N-1, 0, mid).
  But the JOINT LP (exists ANY HD(N) solution + adjacent-shift split to HD(N-1)) is FEASIBLE for N=3..10,12,16
  (shrink_joint.py) -> shrinkability is a property of special solutions.  Layer view: "delete endpoint N-1 + per-run
  monotone relabel (labels above the deleted cell's label drop by 1)" maps every N-layer to an (N-1)-layer; its
  inverse (insert endpoint, choose the new cell's label l_s in each run) maps (N-1)-layers to N-layers.  So a
  GROWING LEMMA "every HD(N-1) solution Z is the shrink of some HD(N) solution" would prove HD(n) for all n.
- GROW test (grow_lp.py): given Z in HD(n), exists Y in HD(n+1) whose adjacent-shift shrink is Z?  Mostly NO for
  n>=6 (xor 8, thg 7/9, stu3 3..9 fail).  TOWER tests: HD(1)<-HD(2)<-...<-HD(N) with right-endpoint shrinks
  (tower_lp.py): feasible only N<=5; two-sided (average of left and right endpoint deletion, tower2_lp.py): N<=6.
  => shrinking/growing lemmas with adjacent hook shifts cannot be iterated; direction (1) closed negatively.
- EXACT certificates via T/H/G + explicit image kernel for hooks 0..A (thg_exact.py; A = last hook where the
  image kernel is >= 0 and the rest stays LP-feasible), checked by stu3/coord_check_hook.py: see certs/thg_run.log.
- T/H/G with SEPARATELY normalised probability kernels (sum_a T(s,a) = sum_a H(t,a) = sum_a G(s,a) = 1) is still
  LP-feasible, n = 5..41 odd (thg_sep.py).  Clean statement ("two-token construction"): every cell carries a run
  token (level |i-j|) and an antidiagonal token (level m'(i+j), or the run on the main antidiagonal); each token draws
  a hook from its kernel; the cell's hook is either token's draw with prob 1/2.
- LEMMA (image hooks, proved): for a <= (n-1)/2 the image kernel satisfies 0 <= T_s <= 2/(n-s) (downward induction:
  (n-s)T_s = 2 - 2 sum_{t=s+1,s+3..<=a} T_t >= 2 - 2 (a-s+1)/(n-a) >= 0), so Y_a = 1/2 T(|i-j|) + 1/2 T(m'(i+j)) is a
  valid hook (runs exact by the recursion, rows constant by the row-independence lemma).
- Continuum self-similarity: after the hooks <= beta, the conditional label law of every token of level <= beta is
  the SAME law 2(1-b)/(1-beta)^2 on (beta,1] -> the upper hooks form a rescaled copy of the whole problem with the low
  levels collapsed; a discrete version of this is the natural route to an all-n proof (not completed).

## STATUS (end of session)
- NO all-n proof.  Direction (1) (shrinking/growing with adjacent hook shifts) closed NEGATIVELY (see above).
- Direction (2): explicit STRUCTURED construction "T/H/G two-token ansatz" reduces HD(n) to O(n^2) kernel unknowns
  (vs O(n^3)); LP-feasible for every tested n; lower ~77% of the hooks are the explicit image kernel (A values:
  n=21:14, 31:22, 41:31, 49:38).  Proved pieces: layer lemma, IG criterion, row-independence lemma, image-hook lemma
  (a <= (n-1)/2).  Open: feasibility of the T/H/G system for all n (suggested: discrete version of the continuum
  self-similarity of the upper hooks).
- EXACT certificates (independent checker stu3/coord_check_hook.py): certs/thg_n*.txt (+ thgb_/thgc_ from parallel
  jobs), logs certs/thg_run*.log; final re-check: verify_all.py.
- FINAL (verify_all.py): every certificate file certs/thg*_n*.txt passes the INDEPENDENT exact checker; odd n certified:
  ALL odd n = 3..61 (T/H/G + image kernel; A(61)=48).  With the Doubling Lemma: every n whose odd part is <= 61
  (in particular all n <= 62, and 64).  Background jobs (PIDs 106996/64056 ascending to 81, 112092/110320 descending
  81..63) continue writing certs/thg_n*.txt / thgb_n*.txt, logs certs/thg_run.log / thg_run_b.log.

## Phase 2 (coordinator: prove T/H/G feasible for every n; certs 3..61 re-verified by coordinator)
- Reformulation (coordinator obs.): Phi_a(s) = (n-s)T(s,a) + [n-s odd]G(s,a), psi_a(s) = 2[s<=a] - Phi_a(s);
  H(t,a) = (psi_a(t-1) - psi_a(t+1))/2  (so H>=0 <=> Phi_a nondecreasing along parity classes of s<=a and
  Phi_a(a), Phi_a(a-1) <= 2).  Rows: with D = T-H split into D_sym + D_anti w.r.t. t <-> n-t:
  G(u,a) = K'_a - 2 E_anti,a((n-1-u)/2), E_anti(k) = sum_{t<=k} D_anti(t)  (D_sym is free).
- Continuum: kernel 2(1-b)/(1-l)^2 has UNIFORM HAZARD 2/(1-b) for all active tokens.  Discrete uniform hazard
  h_a = 2/(n-a+1) gives K_U(l,a) = 2(n-a)/((n-l)(n-l+1)) (law of the min of a random 2-subset of {l..n}).
- T fixed to K_U or to the max-of-two-uniforms kernel M(s,a) = (2(n-1-a)+1)/(n-s)^2 (H,G free): INFEASIBLE n=5..21.
- F-parametrisation: F(s,a) = sum_{t = s+1,s+3,..} H(t,a), phi = 1-F:  T(s,a) = (2phi(s,a) - [n-s odd]G(s,a))/(n-s),
  H(t,a) = phi(t+1,a) - phi(t-1,a), phi(s,a)=1 for s>a.  Then sum_a H(t,a) = 1 AUTOMATICALLY once T,G are normalised
  (Psi(s) = sum_a phi(s,a) = (n+s)/2).  phi = (2(n-a)-1)/(2(n-s)) gives T = M and normalised T,H, but the rows force
  D = T-H = 0 EXACTLY on levels t < (n-1-a)/2 (G(u,a)=0 for u>a), i.e. the recurrence
  (n-t)(phi(t+1)-phi(t-1)) = 2 phi(t) - [n-t odd] G(t,a) there -> the oscillating image kernel unless G forces it.
- Tested: G(u,a) independent of u for all hooks a < n-1-k: infeasible (k=0 all n; k=1 for n>=11; k=2 fails n>=21).
- Coordinator hint (b): image prefix b <= A, residual rho(l) = 1 - sum_{b<=A} kappa_b(l); SELF-SIMILARITY IDENTITY
  L(s) := (n-s)rho(s) + 2 sum_{t=s+1,s+3..<=A} rho(t) = N' - [A-s even], N' = n-A-1 (verified by summing the lower
  run equations).  Product ansatz K(l,a) = rho(l) phi(a) for all low tokens; long runs s>A = runs of an N'-box.
- Product ansatz (all low tokens share one law phi on the upper hooks, A=(n-1)/2): identity L(s) verified exactly,
  rho >= 0 (min = rho(0) ~ 0.2), but the LP is INFEASIBLE for n=5..41 (also variants: level 0 free, c free hooks,
  smaller A) -- selfsim.py, selfsim2.py.  Violations sit on the short even runs / middle rows (selfsim_diag.py).
- min sum|T-H| with image prefix (thg_minD.py, n=13): D = T-H is essentially a SINGLE-LEVEL DIPOLE per hook:
  D(t,a) = delta_a [t=a] with G(u,a) = delta_a for u <= 2a-n-1 (forced by rows), except near the top hook.
- Dipole ansatz (D(.,a) supported at t=a for all but the top k hooks): feasible with k=2 up to n=17, k=3 up to 31,
  fails n=41 (thg_dipole.py).  Banded D (t in [a-w,a+1], top hook free): needs w growing with n (thg_band.py).
  => the top boundary layer is not O(1) hooks in the T/H/G frame.
- RECURSION IDEA (derived here): with A = floor((n-1)/2) image prefix, N' = n-A-1, map fresh tokens (levels > A,
  long-run G) to an N'-box T/H/G solution (T',H',G') by shifting levels by A+1.  Long runs = N'-box runs exactly.
  Upper rows reduce to  E'(k) + G(u(k),a) = C_a  with E'(k) = D'(0) + E_{N'}(k); consistent with the N'-box row
  condition iff the N'-box solution has PROPERTY (P): T' = H' on all levels t' <= (N'-1)/2 (all hooks).  The n-box
  solution then has (P) automatically (reservoir levels <= A have T = H).  Remaining unknowns: reservoir kernels,
  extra token H(A+1,.) (=t'=0), short-run G's; equations: two parity classes of short runs per upper hook.
  (Product reservoir + D'(0)=0 fails at the first upper hook when N' is odd: T'(0,0) = 2/M vs 2/(M+1).)
- PROPERTY (P) (T=H on levels <= (N-1)/2 for all hooks) is LP-INFEASIBLE for most N (5,6,7,10..15,20,21,25,31,41),
  so the naive recursion "fresh tokens = an N'-box solution" cannot close: the upper problem has ONE-SIDED rows
  (E'(k) + G(u(k),a) = C_a) and is a different family.  Reservoir reduction (derived): if the fresh part is fixed,
  the reservoir kernel of upper hook a solves the image recursion with parity-class RHS (beta_0(a), beta_1(a)),
  T(.,a) = beta_0 u0 + beta_1 u1, and its normalisation to rho is AUTOMATIC from the identity L(s).
- Float evidence (thg_prefix_evidence.log): T/H/G with separately normalised kernels and hooks 0..(n-1)/2 fixed to
  the image kernel is LP-feasible for ALL odd n = 7..85 so far (n=5 needs a smaller prefix); also with the longest
  nonnegative image prefix (~0.78n).
- Explicit smooth kernels for the fresh tokens (uniform hazard for fresh T or fresh H): infeasible.  Product ansatz
  also infeasible with the weak cell condition.
- **Reservoir T=H is needed to fail only in the TOP TWO hooks**: with hooks 0..(n-1)/2 = image kernel and
  T(t,a)=H(t,a) for all t <= (n-1)/2 and all hooks a <= n-3, the LP is feasible for n = 9..41 (upper_resTH_notop.py;
  top hook alone suffices for n = 9, 17).
- Structure with top two hooks free (upper_struct.py): S1 (reservoir T=H for a<=n-3) feasible n=9..61;
  S2 (+ short-run G(u,a) independent of u<=A) and S3 (+ T=H on all levels <= 3(n-1)/4) feasible for n=31..61
  (not for n<=25); S4 (+ common reservoir law) infeasible.  Under S2 the RESERVOIR LEMMA applies: the reservoir part
  of hook a is beta_0(a) u0 + beta_1(a) u1 (u_p = image recursion with RHS = indicator of parity class p), and its
  normalisation to rho is automatic.  u0,u1 have small negative entries (min ~ -0.02..-0.09).
- DIPOLE HOOKS: image prefix + for a in [A+1, n-1-k]: D(t,a)=0 for t != a (and H(a+1,a)=0) + short G const:
  feasible with k=4 free top hooks for n = 31, 41, 51, 61 (k=3: 31 only).  Derivation: such a hook is a
  "delta-modified image kernel": T(.,a) solves (n-s)T(s) + 2 sum_{t=s+1,s+3..<=a} T(t)
  = 2 + 2 delta_a [s !== a mod 2, s<a] - delta_a [n-s odd, s <= 2a-n-1],  H = T except H(a,a) = T(a,a) - delta_a,
  G(u,a) = delta_a [u <= 2a-n-1]  (rows automatically constant).  ONE parameter per hook.
- EVIDENCE COMPLETE: T/H/G with image prefix A=(n-1)/2 (proved part) is LP-feasible for ALL odd n = 7..101
  (thg_prefix_evidence.log); also with the longest nonnegative image prefix (A = 81 at n=99, 83 at n=101).
- Dipole structure (+S2) needs k free top hooks: k=4 for n<=61, k=5 for n=71,81, k>5 for n=101 (slowly growing).
- DELTA MODEL (delta_model.py): hooks <= (n-1)/2 image kernel; hooks (n-1)/2 < a <= n-1-k delta-modified image
  kernels (one scalar delta_a >= 0 each); top k hooks = general remainder.  LP-feasible with minimal k:
  k=2 (n<=17), 3 (n<=31), 4 (n=41..61), 5 (n<=81), 6 (n=101) -> the unstructured top layer grows ~log n.
  Nonzero deltas concentrate on the hooks just below the top layer (e.g. n=41: a=33..36 ~0.08-0.21).
- **CANONICAL DELTA** (delta_canon.py): delta_a := the SMALLEST delta >= 0 making the delta-modified image kernel
  nonnegative (explicit rational from the explicit recursion; = 0 while the image kernel is itself >= 0, i.e.
  a < ~0.78n).  Fixing these for (n-1)/2 < a <= n-1-k, the top k hooks still complete (LP): n=21 k>=3, 31 k>=3,
  41 k>=4, 61 k>=4  -- the same minimal k as with free deltas.  delta_check.py: rebuilt full hooks satisfy all HD
  conditions (float, 1e-14).  => fully explicit construction except for the top k(n) ~ log n hooks.
- **EXACT CANONICAL-DELTA CERTIFICATES** (delta_exact.py / delta_driver.py): explicit Fractions for all hooks
  except the top k, exact LP vertex for the top k, full matrices written to certs/delta_n{n}.txt and checked by the
  INDEPENDENT checker stu3/coord_check_hook.py: all odd n = 7..69 PASS (seconds each; logs certs/delta_run_lo.log),
  minimal k: 3 (n=7), 2 (9..13,17,19), 3 (15, 21..33), 4 (35..63), 5 (65..69).  n=71..101 running
  (certs/delta_run_hi.log); float LP: n=81 k=5/6 ok, n=101 k=6 ok (k=5 infeasible).
- Stopped my superseded thg_exact jobs (PIDs 64056/106996, 110320/112092) and the slow no-prefix test.
- Coordinator: independently verified ALL certs/delta_n*.txt (odd 7..101) => HD(n) for all n <= 102.
- Image kernel first-negative hook: n - a_first = 6, 9, 15, 23 at n = 21, 41, 81, 161  ~ 0.78 n^(2/3)
  (oscillating mode of the recurrence grows linearly in n-s; "0.78n" was a small-n coincidence).
- KEY OBSERVATION: every cell off the main antidiagonal pairs a T-token at level s with an H-token at level
  m' == s+1 (mod 2), so the parity-oscillating mode of the image kernel largely CANCELS inside Y_a; only
  Y_a = 1/2(T(s)+H(m')) >= 0 is needed, not T,H >= 0 separately (my LPs imposed the stronger condition).
- PURE IMAGE (all hooks a <= n-2 image kernel, top = residual): residual top hook >= 0 (min ~1/n^2), but hooks
  near the top have negative cells ½kappa_a(s) at low levels s whose partner level m' > a (pureimage*.py).
- Cellwise-nonnegative delta model (delta_cell.py / delta_cell_lp.py): every hook a <= n-2 admits a valid delta,
  but the residual top hook fails for n >= 11 with canonical deltas; with LP-chosen deltas the needed number of
  general top hooks still grows (k=2 to n=25, 3 to 41, >=4 at 51,61).  One parameter per hook is not enough.
- RECURSION TEST (next): embed an N'-box T/H/G solution (N' = (n-1)/2) as the fresh tokens of the upper hooks of
  the n-box (long runs match exactly), image kernel below, solve the RESERVOIR LP (reservoir T,H, extra H(A+1,.),
  short-run G).  Row analysis: rows r < A/2 force D_res(t,a) = D'(t,a') on t < A/2 (+const).
- Recursion test (recursion_test.py): embedding a plain N'-box T/H/G solution (4 different ones) as the fresh part
  of the upper hooks of the (2N'+1)-box: reservoir LP INFEASIBLE for N'=3..10.  Reason: an n-box row r <= A sees
  only the "right half" of the N'-box row r (one-sided rows), which the reservoir cannot compensate.
- RESIDUAL PARITY IDENTITY (proved, any partial T/H/G solution with hooks <= b done, N' = n-1-b remaining):
  (n-s) rho_T(s) + 2 sum_{t = s+1,s+3,..<n} rho_H(t) + [n-s odd] rho_G(s) = 2N'   for every run s <= b
  (sum of the run equations).  Fresh tokens (rho = 1) enter with a PARITY-DEPENDENT count on short runs, so the
  reservoir residuals must oscillate in parity (toplayer.py: rho alternates by a factor ~2 at low levels) -- the
  top layer has to absorb this; this is the discrete obstruction absent in the continuum.
- MODE LP (modes_lp.py; cellwise nonnegativity; hooks > (n-1)/2 = image kernel + signed combination of explicit
  modes: one-sided dipoles at levels a, a-1 (with their G) and symmetric pairs (t, n-t) near the top; TOP HOOK = the
  RESIDUAL, k=1): FEASIBLE for n = 9..41 with m=2 (m=1: fails from n=21).
- **k=1, m=2 mode LP FEASIBLE for n = 51, 61, 81, 101** (top hook = residual; every hook a > (n-1)/2 = image kernel +
  a bounded number (~5) of explicit mode responses).  => bounded-parameter structure, no growing top layer.
- **TWO-DIPOLE CONSTRUCTION**: hooks a <= (n-1)/2 image kernel; hooks (n-1)/2 < a <= n-2: D = c1 e_a + c2 e_{a-1},
  G = c1[u <= 2a-n-1] + c2[u <= 2a-n-3] (c1 >= 0, c1+c2 >= 0), T from the recursion; top hook = RESIDUAL.
  LP over (c1,c2) per hook with CELLWISE nonnegativity: FEASIBLE n = 9..61 (modes2.py dip_a_a1); one dipole
  (dip_a) fails from n=13.
- Two-dipole construction also FEASIBLE for n = 71, 81, 91, 101 and even n = 8..40 (float LP).  LP solutions
  (dip2_inspect.py) zero out the lowest level of the parity class opposite to a (T(0) or T(1)) and use the
  cellwise freedom (T(0,a) < 0 compensated by H/G partners) for the second-highest hook.
- dip2_exact.py: EXACT two-dipole certificates (exact rational dipole coefficients from an LP vertex, exact check of
  every inequality, full matrices -> certs/dip2_n{n}.txt, INDEPENDENT checker): n = 5..21 odd all True.
- dip2 exact certificates: ALL odd n = 5..71, 81, 101 pass the independent checker (seconds each; logs
  certs/dip2_run*.log; 73..99 running).  Files certs/dip2_n{n}.txt.
- Image-hook range can be extended in the proof: with T(t) <= 2/(n-t) (induction), T(s) >= 0 whenever
  sum_{t=s+1,s+3..<=a} 2/(n-t) <= 1, which holds for a <= ~(1-1/e)n.
- Local (greedy, per-hook) rules for the dipole coefficients fail globally: residual top-hook minimum ~ -0.06..-0.08,
  stable in n (a boundary-layer effect).  Hybrid "local min-rule below, global LP over the last K hooks' 2K
  coefficients": K=4 suffices for n=13..41, K=6 at n=61 (dip2_hybrid.py).  Coefficients must be chosen globally
  near the top.
- FINAL (Phase 2): verify_dip2.py -> the two-dipole certificates certs/dip2_n{n}.txt pass the INDEPENDENT checker
  for ALL odd n = 3..101 (n=3: no dipole hooks; n=5: one coefficient).  Each certificate is: image hooks (explicit),
  two-dipole hooks with 2 exact rational coefficients each (from an LP vertex, every inequality re-checked exactly),
  top hook = exact residual.
- CONJECTURE (two-dipole): for every n >= 5 there are reals c1(a) >= 0, c2(a) >= -c1(a), (n-1)/2 < a <= n-2, making
  all hooks of the two-dipole construction (incl. the residual top hook) entrywise >= 0.  Runs/rows/cells hold for
  EVERY choice of c (proved), so feasibility of this O(n)-variable LP IMPLIES HD(n) (not conversely).

## Phase 3 (coordinator: STU needs only UNIF(n,lo,hi) per interval: symmetric, entries in [0,1], runs
##          r_s = #{a in [lo,hi]: a>=s}, rows ((hi+1)^2-lo^2)/n; hi = n-1 solved (J - renewal square))
- Read unif/LOG.md (P-UNIF, Phases 1-2): renewal squares U^m (lo=0) and complements (hi=n-1) PROVEN; half
  construction X exact n<=76 but X>=0 on short runs open; D_ren = U^hi - U^(lo-1) (= sum of IMAGE hooks lo..hi, by
  their two-term identity) fails iff lo > n/2 and K^3 <~ n^2 (K = n-hi-1); T/H/G with termwise T,H,G>=0 LP-feasible
  n<=36, no closed form.  My angle (no duplication): sums of TWO-DIPOLE hooks, interval-dependent coefficients.
- Exact local rule (p3_local.py: minimise 2c1+c2 over the hook's own cellwise constraints): ALWAYS c2 = -c1, i.e.
  the correction is the single "difference-dipole" mode D = c(e_a - e_{a-1}), G = c*[u = 2a-n-1], whose forcing
  2c(-1)^(a-s-1) (s<a) - c[s=2a-n-1] directly counteracts the parity mode.  c_a > 0 only for n-a <~ n^(2/3).
- p3_intervals.py / p3_intervals2.py (exact, n = 9..25): with the LOCAL-RULE two-dipole hooks, the sums over
  [lo,hi] are in [0,1] for EVERY interval with hi <= n-3 (automatically >= 0; <= 1 checked); failures only for
  hi = n-2 (max ~1.078 at two loops near the centre).  D_ren fails for lo > ~n/2 near the top, as P-UNIF found.
- hi = n-2 fixes (p3_hin2.py, exact n=9..25): (b) local-rule hooks lo..n-3 + an INTERVAL-DEPENDENT hook n-2 (two
  free coefficients, only the sum in [0,1]) works for lo >= ~n/2 (fails for small lo, where D_ren works), (c)
  theta-mixtures of D_ren and the local sum fail for a band of lo.  => hi=n-2: D_ren for small lo, (b) for large lo.
- Local rule's binding cells (p3_binding.py): lower bound c_min always at the CENTRE low cells (run 0 or 1 at the
  middle position, parity alternating with a); upper bound at the neighbouring centre cell.  Window c_max-c_min
  shrinks to ~0.005 at a = n-2.
- Coordinator hint: Psi(p) = 1/2 H(p) + (-1)^(L-p) Delta_K + O(K^2/(n-p)^3), Delta_K = 1/2 - K + 2K^2 T_K,
  T_K = sum_j (-1)^j/(K+1+j); image operator L maps 2(-1)^s to 2(-1)^s[n-s odd] (one-class constant) -> a dipole
  at level t0 == n (mod 2) adds exactly D[s == n-1] on the short runs s <= 2t0-n-1, i.e. an alternating T-mode of
  amplitude D: choose D to cancel the parity mode of D_ren.
- R1 (single dipole at the top level of the right parity with the closed-form parity amplitude): fixes ~half of
  the D_ren-invalid intervals (p3_rule1.py).
- **TWO TOP DIPOLES**: U = D_ren(lo,hi) + a*dip(level hi) + b*dip(level hi-1) (free signs; only 0 <= U <= 1 imposed):
  FEASIBLE for EVERY D_ren-invalid interval, n = 13..41 (p3_twolevel.py, float).  Short-run algebra: with alpha =
  amplitude at the level == n (mod 2) and beta at the other, the short-run RHS change is 2beta + (alpha-3beta)[s==n-1];
  parity cancellation needs alpha - 3beta = X := 2A(-1)^n.
- Feasible (alpha,beta) regions are strips NOT containing the naive parity line alpha-3beta = X (p3_poly.py): the
  short-run parity model is too crude (top-boundary effects dominate for the failing intervals).
- TERMWISE version (T,H,G each in [0,1], p3_termwise.py): two top dipoles suffice for ALL intervals with hi <= n-3
  (n = 13..31); hi = n-2 needs the cellwise (parity-cancelling) structure.
- **p3_exact.py**: UNIF(n,lo,hi) := D_ren(lo,hi) (cumulative image kernels C_hi - C_{lo-1}), plus -- only where
  needed -- dipoles at levels hi and hi-1 with rational amplitudes (float max-min LP, rationalised, then EXACT check
  of every cell via parity-class suffix min/max).  Amplitudes -> certs/unif_dip_n{n}.txt.  Includes hi = n-1.
  p3_fullcheck.py rebuilds every full matrix and checks symmetry, [0,1], runs, rows exactly: n=5..25 all OK.
- **EXACT: all n = 2..60, ALL intervals 0<=lo<=hi<=n-1 VALID** (certs/unif_exact_2_60.log; e.g. n=60: 1830 intervals,
  69 need dipoles; 0.5 s per n).  Full-matrix independent re-check (p3_fullcheck.py) n = 5..25, 30, 36, 41: OK.
  n = 61..130 running (certs/unif_exact_61_130.log).
- **EXACT: all n = 2..130, ALL intervals VALID** (certs/unif_exact_61_130.log; n=130: 8515 intervals, 188 corrected,
  5 s).  Dipole region: max K_P = n-hi-1 ~ 0.74 n^(2/3), min lo ~ 0.53 n; #corrected intervals ~ 1.4 n.
- p3_fullcheck.py (independent full-matrix exact re-check) also n = 50, 60: OK.  Extension runs n = 131..256 started
  (certs/unif_exact_131_200.log, certs/unif_exact_201_256.log).
- hi = n-2 (K_P = 1, ~n/2 of the corrected intervals): a FIXED lo-independent amplitude pair works:
  (alpha at level n-2, beta at level n-3) = (1/5,1/7) (also 1/5,1/6 and 1/5,1/8) is valid for EVERY lo, all
  n = 9..201 tested (exact, p3_kp1.py).  For 2 <= K_P <~ 0.74 n^(2/3) no lo-independent pair exists (p3_simple.py).
- n = 256: all 32896 intervals VALID (exact, 48 s); 131..200 and 201..255 still running.

## PHASE 3 SUMMARY / LEMMA LIST (for Lean)
Data: n, 0<=lo<=hi<=n-1, r_s = max(0, hi-max(lo,s)+1); levels s=|i-j|, m'(i,j)=min(i+j+1,2n-1-i-j) (= n iff
i+j=n-1); dipoles: amplitudes D_t (t in L, (n-1)/2 < t <= hi); G(u) = sum_t D_t [u <= 2t-n-1];
T = unique solution of (n-s)T(s) + 2 sum_{t=s+1,s+3,..<=hi} T(t) = 2r_s + 2 sum_{t in L, t-s odd>0} D_t - [n-s odd]G(s)
(s = hi..0; T(s) = 0 for s > hi);  H = T - D;  U(i,j) = (T(|i-j|) + H(m'))/2, resp. (T(|i-j|) + G(|i-j|))/2 on i+j=n-1.
 L1 (runs, PROVED): along run s the levels m' take every t == s+1 (mod 2) in (s, n-1] twice and n once iff n-s odd
    => sum_i U(i,i+s) = r_s.
 L2 (row level multiset, PROVED): {|r-j|} u {m'(r,j)} = circular distances on Z_2n = {0,n} u 2{1..n-1}.
 L3 (dipole row identity, PROVED): t > (n-1)/2 => [r<=t-1] + [r>=n-t] - [n-t<=r<=t-1] = 1 for all r.
 L4 (rows, PROVED): L2+L3 => all rows equal; value ((hi+1)^2-lo^2)/n by total mass (L1).
 L5 (symmetry, trivial).  L6 (cell reduction, PROVED): 0<=U<=1 <=> 0 <= T(s)+H(t) <= 2 for t == s+1, s<t<=n-1,
    and 0 <= T(s)+G(s) <= 2 when n-s odd.
 L7 (P-UNIF, PROVED): no dipoles => T = C_hi - C_{lo-1} (cumulative image kernels = renewal squares, two-term
    identity C_m(p) = 2 Psi_m(p+1)); valid for lo = 0 and for hi = n-1.
 L8 (VERIFIED EXACTLY, n <= 130 and n = 256; runs to 256 continuing): for every interval, either no dipoles, or
    dipoles at levels hi, hi-1 with the rational amplitudes in certs/unif_dip_n{n}.txt give 0 <= U <= 1.
 L9 (VERIFIED n <= 201): for hi = n-2 the fixed amplitudes (1/5, 1/7) work for every lo.
 OPEN (conjecture): all n; remaining analytic core = intervals with 2 <= K_P = n-hi-1 <~ 0.74 n^(2/3), lo >~ 0.53n.
