# P-HOOK research log (Hook Decomposition Lemma for all n)

## 2026-09-28 session start
- Read stu3/LOG.md, coord_check_hook.py, exact_hookdec.py, e17/e18/e22.
- Reformulations noted: (i) reduced form: DS matrices M^s (hooks a>=s x positions), deg_a(r) <= (2a+1)/N, loop automatic.
  (ii) chain of square uniformisations y^(b) = sum_{a<=b} x^(a) monotone.
  (iii) N-integral version: H_a = N x^(a) = sum of 2a+1 involutions (symmetric permutation matrices), run content N per run.
- (m,s) coordinates: cell (p,q) <-> anti-diagonal m=p+q, run s=q-p.  AD(m) = anti-diagonal = involution on window.
  AD(m) U AD(m') with L(m)=a, L(m')=a-1 (L(m)=min(m,2N-2-m)) covers runs 0..a exactly once (zigzag path + loop).

## (resumed after API reset) KEY RESULT: DOUBLING LEMMA (proved + exactly verified)
- Explored explicit families first (all fail somewhere for large hooks):
  pure fold (method of images on Z_2N; hooks = Toeplitz+Hankel with same kernel): unique per hook, parity-oscillating
  kernel, individual hooks a >~ 0.7N go negative (top remainder fine).  "Smooth" variant (rainbow pairs + end caps):
  kappa_a(s) = (N-1-a)/((N-s)(N-s-1)) (s<a), 1/(N-a) (s=a) -- exact discrete analogue of the continuum solution
  k_b(t) = (1-b)/(1-t)^2 (continuum: Y_b(u,v) = K_b(|u-v|)+K_b(u+v), K_b = (1/2)(1-((1-b)/(1-t))^2)_+), off-diagonal
  perfect but LOOPS fail (top hook diag -1/N).  T+H family LP-feasible only with 2 general top hooks.
  N-integral solutions exist (MILP, N<=11); "regular" (all loops 1/N) only for N = 0 mod 4.
- DOUBLING LEMMA: hook decomposition (Y_c)_{c<M} of the M-box  =>  one of the 2M-box (A=[0,M-1], B=[M,2M-1]):
     new hook c   (c<M): (1/2) Y_c on AxA + (1/2) Y_c on BxB
     new hook M+c (c<M): (1/2) Y_{M-1-c} on AxA + (1/2) Y_{M-1-c} on BxB + Y_c on the cross block (cell (i,M+j) <- Y_c(i,j),
                         and its mirror).
  Proof: cross cell (i,M+j) has run M+(j-i), so Y_c (one unit on each diagonal |d|<=c, incl. d=0 = its loop) gives one
  unit on each run M-c..M+c; within part gives runs 0..M-1-c; rows: (2M-2c-1)/(2M) + (2c+1)/M = (2(M+c)+1)/(2M);
  small hooks (2c+1)/(2M); cover: within blocks get 1/2 J + 1/2 J, cross gets sum_c Y_c = J.  QED.
  Verified exactly (doubling.py + hookio.check): M = 1..20 -> 2M = 2..40 all OK.
- REMAINING: odd sizes (need 2M+1 from smaller sizes).

## Odd sizes: negative results (LP, exact-structure tests) -- black-box recursions are impossible
- split N=p+q with p!=q, within blocks = black-box p-/q-hook decompositions (free weights), cross block fully free:
  INFEASIBLE for all tested (2+1,3+2,...,7+6, 3+1, 4+2, 5+3, 6+3); equal splits feasible (= doubling). N=3=2+1 by hand:
  new hook 1 needs run 1 from the 2-box hook H_1 (rows 3/2 > 1) -> contradiction.
- N=2M+1 = A*(M) + m + B*(M): black-box M-hooks on A*,B*, everything else free: INFEASIBLE (M=2..7, several different
  M-box decompositions incl. random LP vertices and doubled ones; M=2 by hand since the 2-box decomposition is unique).
- black-box M-hooks on the cross A*xB* (shift M+1), rest free: INFEASIBLE; (M+1)-hooks on K=[0,M]x[M,2M]: INFEASIBLE;
  (M+1)-hooks on the half A'=[0,M] alone, rest free: INFEASIBLE.  Black-box placements of sizes M,M+1 at all offsets
  + free cells within radius r of m: needs r=M (i.e. everything free).  (Tripling 3M with black-box DIAGONAL blocks
  and free cross IS feasible, 3M<=15; with black-box cross blocks infeasible.)
  => an odd step must use non-black-box structure of the smaller decompositions.
- Near miss (oddstep.py): overlapping doubling of M+1 (halves A'=[0,M], B'=[M,2M] sharing m, cross K shift M) +
  theta-mixing theta=(M+1)/(2M+1) for small hooks + correction tau_c*(theta+1)/2*L, L = Yp_M(A')+Yp_M(B')-Star2,
  tau_c=(2M+2c+1)/((3M+2)M) (c<M), tau_M = 2/(3M+2), sum tau = 1: all equalities hold exactly (rows, runs, cover),
  but nonnegativity fails on middle-vertex cells unless the (M+1)-decomposition has large enough boundary-column
  entries (a boundary invariant not preserved by black boxes).
- Closed form of iterated doubling from n=1 (n=2^k), verified exactly k<=5 (xor_formula.py):
  Y_b(i,j) = 2^{-#{t: i_t=j_t}} * prod_{t: i_t != j_t} [ b_t != b_{s(t)} ],  s(t) = nearest higher bit with i_s=j_s
  (b_s := 0 if none).  (Walsh/XOR structure: Y_b depends only on i XOR j.)
- Remainder test (remlp.py): with small hooks fixed as theta-mixtures U_c = th/2 (Yp_c on A',B') + (1-th)/2 (Y_c on A*,B*)
  (uniform rows (2c+1)/(2M+1), exact), the remainder J - sum U_c (>= ~0.44 cellwise) IS decomposable into the big hooks
  M..2M (LP feasible, 2M+1 <= 17) -- but not with black-box M-hooks on the cross (biglp.py infeasible).  Reason:
  uniform-margin cross structures have zero first moment in d=j-i, while the odd cross windows d in [-1-c, c] have
  first moment -(c+1) -> odd cross parts need tilted margins -> non-black-box within parts.
- Exact certificates for odd n = 21..39 (certs/hookdec_n*.txt, exact_odd.py = stu3 method, 3s..~10min each).
- assemble.py: all n <= NMAX with odd part certified; even n by DOUBLING; every file checked by an
  independent checker stu3/coord_check_hook.check.

## STATUS (end of session)
PROVEN: DOUBLING LEMMA  HD(M) => HD(2M) (explicit, exact), hence HD(m) => HD(2^k m) for all k.
EXPLICIT closed form for n = 2^k (XOR/Gray formula above).
VERIFIED EXACTLY (independent checker): see assemble logs (all n <= 40; all even n <= 80).
OPEN: odd n > 39.  All black-box recursions for odd n are impossible (LP-certified negative results above); an odd
step needs structured (tilted-margin) sub-objects or an explicit family.
- FINAL VERIFICATION (assemble.py 80, log certs/assemble80.log): 60 decompositions written to certs/final_n{n}.txt and
  each checked EXACTLY by an independent checker stu3/coord_check_hook.check: all n = 1..40 and all even
  n <= 80 (odd n <= 20: stu3 certificates; odd 21..39: certs/hookdec_n*.txt; even n: doubling, recursively).
  Also n = 64 via the XOR closed form (pow2check.py), independent check True.
