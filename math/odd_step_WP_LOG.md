# P-HOOK3 research log (HD(n) for all n via strengthened induction / boundary invariant, odd step 2M+1)

## 2026-09-28 session start
- Read hook/LOG.md, doubling.py, oddstep.py, remlp.py, biglp.py, xor_formula.py, hookio.py, stu3/coord_check_hook.py,
  hook2/LOG.md (P-HOOK2: shrinking lemma + smooth explicit solutions -- not duplicated here).
- Plan: (1) re-derive oddstep exactly, extract boundary condition B(M+1); (2) find invariant HD+ preserved by
  doubling and the odd step; (3) exact verification n <= 100+.

## Near-miss analysis (hook/oddstep.py), exact bookkeeping
- Notation: n=M+1 box Yp (rho-symmetric), boundary column g_a(r) = Yp_a(M-r, M) (run r), kappa_c = tau_c(1+th)/2
  = (2M+2c+1)/(2M(2M+1)) (c<M), 1/(2M+1) (c=M).  Star cell at distance s>=1 from m in big hook M+c:
  1/2 g_{M-1-c}(s) [s<=M-1-c] or g_c(M-s) [s>=M-c]  minus  kappa_c (1-g_M(s)).  Loop(m): g_{M-1-c}(0) - 2kappa_c(1-g_M(0)).
- OBSTRUCTION 1 (loop, any input): sum_{c<M} loop_m(hook M+c) = -(1-g_M(0))(M-1)/(2M+1) < 0 for M>=2.
  So NO boundary condition on the input can make the near miss nonnegative (N>=5).  (Hook 2M has loop ~1 at m.)
- OBSTRUCTION 2 (star, any input): summing the star conditions over c<=M-1-s needs sum_{c<=M-1-s} kappa_c <= 1/2,
  false for s < (2-sqrt3)M.  => the uniform correction tau_c*L is the wrong mechanism.
- Reformulation: star entries = slacks of the non-star rows; a big-hook correction P_c on A*xA* must satisfy
  (F2) row_{P_c}(j) - class_{M-j}(P_c) = delta_c (delta_c = row deficit; delta_M = M/((2M+1)(M+1))!), and
  star_c(s) = base_c(s) - class_s(P_c) >= 0.
- fill_lp.py (P_c = pieces of (1+th)/2 Yp_M): infeasible for LP-cert and doubled inputs (N>=5 resp. >=11).
  joint_lp.py (input Yp ALSO free, HD(M+1) constraints): feasible M+1 = 4..15, INFEASIBLE M+1 >= 16
  (max common slack -1.7e-4 at 16, -1.0e-3 at 20).  => fill-by-top-hook skeleton dead for large M, for ANY input.
- joint_lp2.py (within-A* parts of big hooks FREE): feasible M+1 <= 24, slack ~0.25/M.

## KEY RESULT: odd step modulo the WITHIN PROBLEM (WP)  [oddstep_wp.py, exact_wp.py]
- Skeleton (N=2M+1, A'=[0,M], B'=[M,2M], A*=[0,M-1], B*=[M+1,2M], m=M, K=A'xB' with cell (i,M+j) <- Yp_c(i,j)):
    small c<M : th/2 (Yp_c on A', mirrored on B') + (1-th)/2 (Y_c on A*, mirrored on B*),  th=(M+1)/(2M+1)   [explicit]
    big M+c   : W_c on A*xA* (mirrored on B*xB*) + Yp_c on K minus its star cells                    [K explicit]
                star cells (x,m) := row slack, loop(m) := run-0 slack.
- All equalities <=> W = (W_0..W_M) solves the WITHIN PROBLEM WP(Yp) on the M-box A*:
    (a) sum_c W_c = 1/2 J + th/2 Yp_M|A*
    (b) row_{W_c}(j) - class_{M-j}(W_c) = rho_c - 1/2[j >= c+1],   rho_c = M(2M-2c+1)/((M+1)(2M+1))
    (c) class_s(W_c) <= 1/2 for s <= M-1-c and s = 0;  class_s(W_c) <= g_c(M-s) for M-c <= s <= M-1
  (star entry at distance s of hook M+c = cap_c(s) - class_s(W_c); loop(m) = 1 - 2 class_0(W_c)).
  Only data used from Yp: its top hook on A* and its boundary column g.  Y (M-box) only enters the small hooks.
- WP feasible for: all LP-certificate inputs (M+1<=20), all doubled inputs, 42 random LP-vertex inputs (M+1<=12),
  and along the whole self-generated recursion (float, recursive_float.py: all n <= 70 OK).
- CONJECTURE (WP): WP(Yp) is feasible for every rho-symmetric HD(M+1) decomposition Yp.  Together with the proven
  Doubling Lemma this would give HD(n) for all n.  (Not proven; WP is an LP on the M-box with ~M^3/2 variables.)
- Weighted-gluing observation: with vertex weights (1,..,1,1/2) on A' and (1/2,1,..,1) on B' the overlap is exactly
  consistent (row m automatic), but the cross block then has weighted center M/(2M+1) (first-moment obstruction:
  unit windows [1-c,c] impossible, LP-confirmed infeasible for n>=3); fractional windows needed.  Not pursued further.

## EXACT verification of the WP odd step
- exact_wp.py: HiGHS dual-simplex vertex of WP -> exact rational solve on the support (sympy sparse rref) -> exact check
  of WP -> exact assembly (Fractions) -> file -> coordinator's INDEPENDENT checker stu3/coord_check_hook.check.
- exact_pipeline.py (self-contained recursion from D(1)=[[1]]: even n by DOUBLING, odd n by WP odd step with the
  recursion's own outputs as inputs): ALL n = 2..32 verified exactly by the independent checker (certs/rec_n*.txt,
  certs/pipeline64.log).  Denominators grow fast along the recursion (~1e34 at n=31); n=33 (M=16) exact solve 188 s,
  pipeline stopped there (killed own PID).
- exact_batch.py (inputs = verified hook/certs/final_n{M},{M+1}, rho-symmetrised): N = 41 verified exactly (53 s,
  certs/wp_n41.txt).  Batches for M = 21..26 running at session end (certs/batch_[abc].log).
- Float: recursive_float.py all n <= 70 OK (WP feasible at every odd step).

## STATUS (end of session)
- No boundary invariant rescues the near miss (two input-independent obstructions + joint-LP infeasibility M+1>=16).
- NEW REDUCTION: HD(M) & HD(M+1) & WP(Yp) feasible  =>  HD(2M+1), explicit except the within-parts W_c (an LP on the
  M-box).  WP was feasible for EVERY input tried (LP certs, doubled, random vertices, recursive outputs) -> conjecture:
  no invariant needed; the missing piece is a proof that WP(Yp) is feasible for all rho-symmetric HD(M+1) Yp.
