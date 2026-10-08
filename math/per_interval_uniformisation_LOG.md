# P-UNIF research log (weaker lemma UNIF(n, lo, hi) for the Kirwan-free STU proof)

LEMMA UNIF(n, lo, hi), 0 <= lo <= hi <= n-1: symmetric n x n matrix u, entries in [0,1],
run sums sum_i u(i,i+s) = r_s := #{a in [lo,hi] : a >= s} (s >= 0, loop = run 0),
all row sums R := ((hi+1)^2 - lo^2)/n.

## 2026-09-28 session start
- Read stu3/LOG.md, STUProof/KirwanFreeHook.lean (unif, unif_smaj), KirwanFree.lean (compG uses
  crosses [M-m, M] in box M+1 (hi = n-1) and crosses/squares with hi < k <= M' in boxes M'+1).
- E1 (e1_renewal_square.py): RENEWAL construction for squares [0,m] in box n >= m+2 (reversal-block flow =
  stationary renewal process of block boundaries): K = n-m-1, H(l) = 1 - K^2/((n-l)(n-l+1)) (1<=l<=m+1),
  blocks [0,l-1] and [n-l,n-1] weight H(l), interior blocks [a,a+l-1] (1<=a<=n-1-l) weight H(l)-H(l+1);
  u = sum w_B * antidiag(B).  EXACT check (Fractions) all n<=60, 0<=m<=n-1: 0 failures.
- Crosses as differences U^hi - U^(lo-1) of renewal squares: negative entries in 326/4495 cases (n<=30), region
  hi >= ~0.75n, K_hi = n-hi-1 small, lo close to hi (hi = n-2: lo >= ~0.55n). Mechanism: parity (a reversal block
  of length l only hits runs s = l-1 mod 2); U^(n-2) has a dip ~0.38 on the central antidiagonal i+j=n-1.
- E2 (e2_feas.py): full UNIF LP feasible for ALL core cases hi+2<=n<=min(2hi+1,40): 7790 LPs, 0 infeasible;
  smallest margins at squares [0,n-2] (~0.0018 at n=40).
- E3: in the failing region, V <= U_ren(hi) (V any square [0,lo-1] unif) and U >= V_ren(lo-1) both LP-feasible
  (all 187 cases n<=24).  Pure reversal-block flows for crosses: infeasible whenever lo > n/2 (no partition of n
  into parts in [lo,hi+1]); for the complement arm set [0,lo-1] u [hi+1,n-1]: feasible 122/150 (fails at hooks).
- E4 (image/Toeplitz+Hankel u(i,j)=C(j-i)+C(i+j+1), C even on Z_2n): rows automatic, unique solution per profile;
  works for squares, fails in the same region as the renewal difference (parity mode: the recursion has the exact
  homogeneous solution c_s = (-1)^s; hooks near the top get amplitude ~1/K >> smooth part ~K/n^2).
- E8/E9/E11 (E/S family: image blocks E_k + 'shift' blocks S_k = full run k + middle reversal): LP-feasible for all
  core cases n<=20; one-parameter top-S family has a feasible theta for all core cases n<=36 but intervals shrink ~1/n.
- E10/E13/E14 parity-free blocks (boundary 1/2(rev[0,k-1]+rev[0,k-2]+loop)): smooth closed form
  c_s = 1/2 - K(K-1)/(2(n-s)(n-s-1)), but loop over-supply for crosses (c_0 = -w(lo+hi+1-n)/(n(n-1))).
- E16-E21: window pieces J[t,t+hi] - Ren_{lo-1}(sub-box) (entries automatically in [0,1]).
- **E25/E26 KEY: SUB-BOX RENEWAL family** X = sum pi Ren_hi(sub-box) - sum phi Ren_{lo-1}(sub-box): rows and <=1 are
  automatic; scanning (sub-box size c, phi) with uniform offsets: (c = hi+1, phi = 1/2) works for EVERY cross, n<=26.
- **E27 HALF CONSTRUCTION** (float scan all 0<=lo<=hi<n, n<=44: 0 failures):
    X = theta U^hi_n + (1-theta) avg_t J[W_t] - 1/2 U^{lo-1}_n - 1/2 avg_t Ren^{(b)}_{lo-1}[W_t],
    b = hi+1, W_t = [t,t+hi], t uniform on 0..n-b, theta = 1 - lo^2/(2b^2)
  = average of the renewal difference and the uniform-window construction.  Rows = ((hi+1)^2-lo^2)/n, run sums and
  X <= 1 hold by construction (proof: 3 lines); only X >= 0 is not proven (reduces to lo=0: renewal, hi=n-1: J-Ren).
- verify_half.py: EXACT verification (integer-scaled rationals; renewal cell formula cross-checked vs block
  construction c<=16; negative controls: pure renewal difference FAILS at (12,10,10) with -1/10 [note 2026-09-28: -1/10 occurs at cells (2,9),(9,2); the minimum entry is -677/4620 at (5,6),(6,5)], perturbed theta
  fails rows).  RESULT: all 0<=lo<=hi<n, n<=60: 37820 cases, 0 failures (verify_half_1_60.log);
  n = 61..76 in verify_half_61_76.log.
- Margin: min entry of X on runs s<lo (hi<=n-2) ~ 2.1/n^2 (at the hook lo=hi=n-2), stable n=20..60
  (full-LP optimum margin is ~3/n^2) -> construction is near-optimal, no drift.

## STATUS (end of session)
PROVEN all n: renewal squares U^m_n (UNIF(n,0,m)), complements J-U^{lo-1}_n (UNIF(n,lo,n-1)); for the HALF
construction X: symmetry, run sums, row sums, X<=1, X>=0 on runs >= lo, and X>=0 when lo=0 or hi=n-1.
OPEN: X >= 0 on the short runs s<lo for 1<=lo<=hi<=n-2 (verified exactly n<=60, 0 failures).
Proof of the renewal square (for the report):
 (i) H(l)-H(l+1) = 2K^2/((n-l-1)(n-l)(n-l+1)) >= 0 (l<=m), H(m+1) = 1/(K+1) -> weights >= 0, H <= 1;
 (ii) flow: into interior node p: H(p) + sum_{l<p}(H(l)-H(l+1)) = H(1); out of p: H(n-p) + (H(1)-H(n-p)) = H(1)
      -> every point covered by the same total weight -> constant rows;
 (iii) length totals (n+1-l)H(l) - (n-1-l)H(l+1) = 2 (l<=m), (n-m)H(m+1) = 1 (l=m+1); a reversal block of length
      l hits runs l-1, l-3, ... once -> run s gets m+1-s; rows then = (m+1)^2/n by mass count;
 (iv) blocks through a cell are concentric; at most one boundary block, longer than every interior one ->
      cell <= sum_{l>=s+1}(H(l)-H(l+1)) (telescoped, one parity only) + H(boundary) <= H(s+1) <= 1.
- FINAL exact verification of the HALF construction: n<=60: 37820 cases; n=61..76: 38256 cases; total 76076
  (all 0<=lo<=hi<n), 0 failures (verify_half_1_60.log, verify_half_61_76.log).

## Phase 2 (2026-09-28): proof of X >= 0 on short runs (or robust modification)
- X was re-implemented independently from the report formulas (coord/coord_check_X.py): 816 cases n<=16 exact OK.
- P2 (p2_rays.py, p2_netweights.py): RAY LEMMA. Every reversal-block construction X = sum_B x_B rev(B); a cell (i,j)
  equals the sum of the net weights x_B of the concentric blocks [i-k, j+k] (k = 0..min(i,n-1-j)); x([i,j]) =
  X(i,j) - X(i-1,j+1). If non-terminal short blocks have x_B <= 0, the minimum over short cells on each antidiagonal
  is at run 0/1 (+ terminal cells).  Half construction: sign condition holds n<=22, fails at blocks adjacent to the box
  edge (a=1) for n>=23 (p2_signcheck2.log).  D_ren: sign condition holds always (alpha^P_l < alpha^N_l).
- Pairwise/monotone bounds on the f-representation fail (large negative pairs); window monotone bound fails at centre.
- LP: optimal short-run margins: hooks lo=hi=n-2 ~8.5/n^2 (inherent Theta(1/n^2)), hooks lo=hi=n/2 ~0.83/n,
  (n-3,n-2) ~22/n^2.  So a 'robust c/n margin' is impossible near the top; the half construction has only ~2/n^2
  at lo=hi~n/2 (tent effect of the uniform windows).
- **T/H/G ansatz with TERMWISE T,H,G >= 0** (p2_thg_pos.py): LP-feasible for ALL core cases n<=24.  Then cells
  T(s)+H(m') >= 0 are trivially nonnegative -> positivity reduces to 1D sequence conditions.
- **TWO-TERM (IMAGE) IDENTITY for renewal squares** (p2_image_identity.py, exact, 206770 cells, c<=30):
    U^m_c(i,j) = Psi(|i-j|+1) + Psi(m'+1),  m' = min(i+j+1, 2c-1-i-j),  Psi(p) = sum_{l>=p} (-1)^(l-p) H(l)
  (proof: the ray sum H(s+1)-H(s+2)+...+H(m') equals Psi(s+1)+Psi(m'+1) since m'-s is odd).
  Hence renewal square = pure image kernel (E4), and D_ren = U^hi - U^(lo-1) has cells C(s)+C(m') with the 1D
  sequence C(p) = Psi_P(p+1) - Psi_N(p+1):  D_ren valid  <=>  C(p) >= 0 for 0<=p<=n-2  (1D criterion; C(n-1)=C(n)=0).
  C(p) >= 0 automatically for p >= lo (alternating tail of the decreasing H_P); for p < lo it is a delicate
  cancellation of O(1/K^2) parity terms against Delta*g ~ K/n^2 -> fails iff K^3 <~ n^2 (matches E20).
- Image family + free constant g on the main antidiagonal (p2_image_g.py): does NOT fix the bad region.
- T/H/G with G == 0 suffices except odd n, lo=hi=n-2 (needs small G>0).  TV-minimal and max-min LP solutions
  (p2_thg_smooth.py, p2_thg_maxmin.py, p2_thg_near.py): no evident closed form (large H(K) and top corrections).
- T/H/G with termwise T,H,G >= 0: LP-feasible for ALL core cases n <= 36 (p2_thg_pos.py, p2_thg_pos_25_36.log).

## PHASE 2 STATUS (end)
NOT a complete all-n proof of X >= 0.  Rigorous new lemmas (all n):
 (L1) two-term identity U^m_c(i,j) = Psi(|i-j|+1) + Psi(m'+1) (renewal square = image kernel);
 (L2) D_ren = U^hi_n - U^(lo-1)_n is a valid UNIF(n,lo,hi) iff the 1D sequence C(p) = Psi_P(p+1) - Psi_N(p+1)
      is >= 0 for p < lo (automatic for p >= lo); fails exactly in the region K^3 <~ n^2, lo > n/2;
 (L3) ray lemma (cells = sums of net block weights along concentric blocks) -> for D_ren only runs 0,1 matter;
 (L4) T/H/G reduction: u(i,j) = T(|i-j|) + H(m') (+G on i+j=n-1) with T,H,G >= 0 solving the 1D linear system
      [runs: (n-s)T(s) + 2 sum_{m=s+1 mod 2, m>s} H(m) + [s=n-1 mod 2] G(s) = r_s;
       rows: E(r)+E(n-1-r)+G(|n-1-2r|) = const, E(k) = sum_{t<=k} (T-H)(t); cells <= 1]
      is a valid UNIF with trivial positivity.  LP-feasible for all core cases n <= 36; no closed form found.
 Half construction X: exact n <= 76 (76076 cases); its tight cells are loops of hooks (~2.2/n^2), inherent
 Theta(1/n^2) near the top (LP optimum ~8.5/n^2 at lo=hi=n-2), so any proof must be second-order exact there.
