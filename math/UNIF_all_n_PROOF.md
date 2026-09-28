# Proof: interval uniformisations exist for every n (UNIF(n, lo, hi) for all n)

This is the last ingredient of the Kirwan-free proof of the STU conjecture in every dimension: with the machine-checked reduction `stu_exists_of_intervalUnif` (lean/STUProof/KirwanFreeU.lean) it gives symmetrically thermalizing unitaries in all dimensions without Kirwan's theorem. Status: complete paper proof; the only computer inputs are the one-parameter facts F1–F6, verified exactly by two independent methods (code/verify_facts.py and code/coord_facts.py). Formalised in Lean: `intervalUnifAll_all` (lean/STUProof/UnifAllN.lean, with DipoleUnif.lean and UnifFacts.lean), which yields the hypothesis-free theorem `stu_exists_unconditional` (lean/STUProof/KirwanFreeFinal.lean).

=====
# THE PROOF: UNIF(n, lo, hi) FOR ALL n  (P-PROOF, 2026-09-28)
====================================================================================================================

THEOREM.  For all integers n >= 1 and 0 <= lo <= hi <= n-1 there is a real symmetric n x n matrix U with
0 <= U(i,j) <= 1, run sums  sum_{i=0}^{n-1-s} U(i,i+s) = r_s := #{a in [lo,hi] : a >= s}  (0 <= s <= n-1), and
all row sums equal to ((hi+1)^2 - lo^2)/n.

Notation: K := n-1-hi (>= 0), M := n-lo.   CASES:
 (A) hi = n-1:   U = J - U^{lo-1}_n (lo >= 1), U = J (lo = 0)            [P-UNIF, proved for all n]
 (B) lo = 0:     U = U^{hi}_n (renewal square)                            [P-UNIF, proved for all n]
 otherwise 1 <= lo <= hi <= n-2, hence K >= 1 and K+1 <= M <= n-1, and
 (C) n <= 2K+1  (<=> 2hi <= n-1):  T/H/G construction WITHOUT dipole (= D_ren); K >= 2 by Sec. 7, and
                                   K = 1 forces (n,lo,hi) = (3,1,1), checked by hand in Sec. 7.
 (D) n >= 2K+2, K = 1 (hi = n-2):  ONE dipole at level hi, amplitude alpha = 2/7.
 (E) n >= 2K+2, K >= 2:            ONE dipole at level hi, amplitude alpha* (Sec. 5).
No finite computer enumeration over n is needed (N0 = 3); the only computer-verified inputs are the
one-parameter facts F1-F6 (Sec. 3), verified exactly for ALL K by verify_facts.py.

--------------------------------------------------------------------------------------------------------------------
## 1. The T/H/G construction with at most one dipole  (= hook2 Phase 3 L1-L6, specialised; proofs included)
Fix n, lo, hi with hi <= n-2, and alpha >= 0; if alpha != 0 assume 2*hi >= n.  Put t := hi,
  D(u) := alpha [u = t]  (1 <= u <= n-1),   G(u) := alpha [u <= 2t-n-1]  (0 <= u <= n-1, u = n-1 mod 2).
T : {0..n-1} -> R:  T(s) := 0 for s > hi, and for s = hi, hi-1, ..., 0
  (RUN)  (n-s) T(s) = 2 r_s - 2 sum_{t' in (s, n-1], t' = s+1 (mod 2)} H(t') - [n-s odd] G(s),   H(u) := T(u) - D(u).
  m'(i,j) := min(i+j+1, 2n-1-i-j);   U(i,j) := (T(|i-j|) + H(m'(i,j)))/2  if i+j != n-1,
                                     U(i,j) := (T(|i-j|) + G(|i-j|))/2    if i+j  = n-1.
LEMMA 1.1 (levels).  |i-j|+1 <= m'(i,j) <= n,  m'(i,j) = |i-j|+1 (mod 2),  m' = n iff i+j = n-1.
 For fixed s the multiset {m'(i,i+s) : 0 <= i <= n-1-s} contains every t' in (s, n-1] with t' = s+1 (mod 2)
 exactly twice, and n exactly once iff n-s is odd.
 Proof: v = 2i+s+1 runs over {s+1, s+3, ..., 2n-1-s}, a set invariant under v -> 2n-v; m' = min(v, 2n-v).
LEMMA 1.2 (runs).  sum_i U(i,i+s) = r_s for all 0 <= s <= n-1.
 Proof: by 1.1 the run sum is ((n-s)T(s) + 2 sum H(t') + [n-s odd]G(s))/2 = r_s by (RUN) for s <= hi.  For s > hi:
 T(s) = 0, H(t') = 0 for t' > hi (D is supported at t = hi), G(s) = 0 as 2t-n-1 < t <= hi < s, and r_s = 0.
LEMMA 1.3 (rows).  All row sums are equal (hence equal to ((hi+1)^2-lo^2)/n, since the total mass is
 sum_s (2-[s=0]) r_s = sum_{a=lo}^{hi} (2a+1)).
 Proof: row r: {|r-j|}_j = {0} + {1..r} + {1..n-1-r} and {m'(r,j)}_j = {r+1..n} + {n-r..n-1} (multisets), level n
 only at j = n-1-r where |r-j| = |n-1-2r|.  So {|r-j|}_j + {m'(r,j)}_{j != n-1-r} = {0} + 2*{1..n-1}, and
 2*rowsum = T(0) + 2 sum_{l=1}^{n-1} T(l) - sum_{j != n-1-r} D(m'(r,j)) + G(|n-1-2r|)
          = const - alpha([r <= t-1] + [r >= n-t] - [n-t <= r <= t-1]) = const - alpha,
 because |n-1-2r| <= 2t-n-1 <=> n-t <= r <= t-1, and n-t <= t (2t >= n) makes the bracket identically 1.
LEMMA 1.4 (cells).  U is symmetric.  If  0 <= T(s)+H(t') <= 2  for all 0 <= s < t' <= n-1 with t' = s+1 (mod 2),
 and 0 <= T(s)+G(s) <= 2 for all s with n-s odd, then 0 <= U <= 1.   (By 1.1.)
So the THEOREM in cases (C),(D),(E) follows from the 1-D inequalities of Lemma 1.4.

## 2. x-coordinates and the pair-sum formula
tau(x) := T(n-x), eta(x) := H(n-x) (1 <= x <= n), gamma(x) := G(n-x) (x odd).  The dipole sits at x = K+1:
eta(y) = tau(y) - alpha[y = K+1];  gamma(x) = alpha [x >= 2K+3]  (x odd).  Lemma 1.4 becomes:
  (CELL)  0 <= tau(x) + eta(y) <= 2  for 1 <= y < x <= n, x-y odd;   0 <= tau(x) + gamma(x) <= 2 for x odd.
LEMMA 2.1 (pair sums).  Let K >= 1, K+1 <= M <= n-1, and (alpha = 0 or n >= 2K+2).  Define Q(x) := 0 (x <= K),
   Q(x) := 2x(x-1) - 2K^2 - [x >= M+1](2x(x-1) - 2M^2) + 2(K+1) alpha [K+2 <= x <= 2K+2]   (K+1 <= x <= n).
 Then tau(x) = 0 for x <= K and tau(x) + tau(x-1) = Q(x)/(x(x-1)) for K+1 <= x <= n.
 Proof.  Let tau~ be defined by these relations, T~(s) := tau~(n-s), H~ := T~ - D, and
 E(s) := (n-s)T~(s) + 2 sum_{t'=s+1 (2), s<t'<=n-1} H~(t') + [n-s odd]G(s) - 2 r_s.  Since (RUN) is triangular it
 suffices to show E = 0.  E(n-1) = tau~(1) + G(n-1) = 0.  E(n-2) = 2tau~(2) + 2H~(n-1) - 2r_{n-2} = 2[K=1] + 0 - 2[K=1] = 0
 (Q(2) = 2 if K = 1).  For 0 <= s <= n-3, x := n-s >= 3, using S(x) := tau~(x)+tau~(x-1) = Q(x)/(x(x-1)) (also for x <= K):
   E(s) - E(s+2) = x S(x) - (x-2) S(x-1) - 2D(s+1) + [x odd](G(s)-G(s+2)) - 2(r_s - r_{s+2})
                 = (Q(x)-Q(x-1))/(x-1) - 2alpha[x=K+2] + alpha[x=2K+3] - 2([K+2<=x<=M+1] + [K+1<=x<=M]) = 0,
 since r_s = #{x_a in [K+1,M] : x_a <= x} (x_a := n-a), D(s+1) = alpha[x = K+2], G(s)-G(s+2) = alpha[x = 2K+3] for
 odd x (absent if n < 2K+3), and by direct computation Q(x)-Q(x-1) = (x-1)(2[K+2<=x<=M+1] + 2[K+1<=x<=M]
 + 2alpha[x=K+2] - alpha[x=2K+3]) for all 3 <= x <= n.  Hence E(s) = E(s+2) = ... = 0.  []

## 3. Special functions and the verified facts
 beta(x) := sum_{j>=0} (-1)^j/(x+j) (x > 0);  beta(x) + beta(x+1) = 1/x;  beta(m+1) = (-1)^m (ln 2 - sum_{i=1}^m (-1)^(i-1)/i).
 g(y) := 2/(y(y-1));   sigma(x) := sum_{j>=1} (-1)^(j-1) g(x+j) = 4 beta(x) - 2/x   (x >= 1).
 a(K) := 2/(K+1) - 1 + K^2 sigma(K+1) = 4K^2 beta(K+1) + 1 - 2K = 4K^2 (-1)^K (ln 2 - sum_{i<=K} (-1)^(i-1)/i) + 1 - 2K.
   (a(K) = 2 Delta_K of the coordinator; a(1) = 3-4ln2, a(2) = 16ln2-11, a(3) = 25-36ln2; a(K) ~ 1/(2(K+1)^2).)
 omega(k) := sum_{y=k+1}^{2k} (-1)^y k/(y(y-1))  (rational)  = (-1)^k (2k beta(k+1) - 1) + 2k beta(2k) - 1/2.
   [Proof: omega/k = -sum_{z=k}^{2k-1}(-1)^z/z - sum_{y=k+1}^{2k}(-1)^y/y and sum_{z>=m}(-1)^z/z = (-1)^m beta(m).]
LEMMA 3.1 (alternating sums).  c_0 >= c_1 >= ... >= 0, c_j -> 0  =>  0 <= sum (-1)^j c_j <= c_0; if moreover
 c_j - c_{j+1} is nonincreasing, then c_0/2 <= sum (-1)^j c_j <= c_0/2 + (c_0-c_1)/2.
 (Second part: 2 sum = c_0 + sum (-1)^j (c_j - c_{j+1}), apply the first part.)
LEMMA 3.2 (sigma).  (i) sigma(x) + sigma(x-1) = g(x) (x >= 2);  (ii) 1/(x(x+1)) <= sigma(x) <= (x+4)/(x(x+1)(x+2))
 (Lemma 3.1 with c_j = g(x+1+j), g convex decreasing);  (iii) sigma(x+1) < sigma(x) (sigma(x)-sigma(x+1) = g(x+1)-2sigma(x+1) > 0 by the UPPER bound in (ii): (x+2)(x+3) - x(x+5) = 6 > 0);
 (iv) 1 - M^2 sigma(M) = a(M)  (from (i));  (v) 2M^2 sigma(M+1) + 2/(M+1) <= 2 - 12M/((M+1)(M+2)(M+3)) (from (ii),
 an identity at the bound); in particular Gamma*sigma(x) <= M^2 sigma(M+1) < 1 for x >= M+1, Gamma := M^2-K^2, and
      (vi)  Gamma sigma(M+1) + a(M) = (2M^2-K^2) sigma(M+1) + 2/(M+1) - 1 <= 1 - K^2 sigma(M+1).
LEMMA 3.3 (beta bounds, "Lemma B").  For all real x > 0:  u(x) - eps(x) <= beta(x) <= u(x),
   u(x) = 1/(2x) + 1/(4x^2) - 1/(8x^4) + 1/(4x^6),   eps(x) := u(x)+u(x+1)-1/x = (17x^4+34x^3+29x^2+12x+2)/(8x^6(x+1)^6).
 Proof: d := u - beta has d(x)+d(x+1) = eps(x), d(x+2N) -> 0, so d(x) = sum_j (-1)^j eps(x+j); eps > 0 and
 eps(x)-eps(x+1) = (17x^4+68x^3+100x^2+64x+16)/(x^6(x+1)(x+2)^6) > 0; Lemma 3.1.  []
FACTS (verify_facts.py: exact rational interval evaluation for K = 1..11 via Lemma 3.3 at shifted arguments,
 and for K >= 10 exact polynomial positivity of the Lemma-3.3-substituted inequalities; log verify_facts.log):
 F1  a(K) > 0 (K >= 1).       F2  a(K) > a(K+1) (K >= 1).       F3  a(K) + a(K+1) <= 1/(2(K+1))  (K >= 2).
 F4  w(K) := (-1)^K omega(K+1) > 0  and  (K+1)(a(K) + a(K+1)) <= 4 w(K)   (K >= 2).
 F5  a(1) - 2/21 - a(3) > 0 (>= 0.0854);  a(1) - 2/21 + a(2) <= 2/7 (slack 0.063);  a(1) < 5/21 (slack 0.0107).
 F6  a(1) < 1/4,  a(3) < 1/20.
 Consequences: 0 < a(M) <= a(K+1) < a(K) for M >= K+1;  a(K) < 1/(2(K+1)) for all K >= 1 (F3, F6).

## 4. Closed form of tau
LEMMA 4.1.  In the setting of Lemma 2.1 put  Phi(x) := 1 - K^2 sigma(x) (x <= M),  Phi(x) := Gamma sigma(x) (x >= M+1),
 b(y) := 2(K+1)alpha/(y(y-1)) [K+2 <= y <= 2K+2].  Then for K+1 <= x <= n:
    tau(x) = Phi(x) + (-1)^x e(x),   e(x) := (-1)^(K+1) a(K) + sum_{y=K+2}^{x} (-1)^y b(y) + [x >= M+1] (-1)^M a(M).
 Proof: induction.  x = K+1: tau = Q(K+1)/(K(K+1)) = 2/(K+1) = Phi(K+1) + a(K) (definition of a).  Step: by 3.2(i),
 Phi(x)+Phi(x-1) = (2x(x-1)-2K^2)/(x(x-1)) (x <= M), = 2Gamma/(x(x-1)) (x >= M+2), and at x = M+1 it exceeds
 2Gamma/((M+1)M) by 1 - M^2 sigma(M) = a(M) (3.2 iv); so tau(x)+tau(x-1) = Q/(x(x-1)) = Phi(x)+Phi(x-1) + b(x) - a(M)[x=M+1].
COROLLARY 4.2 (bulk).  If 2K+2 <= n then for x >= max(M+1, 2K+2):  tau(x) = Gamma sigma(x) + (-1)^x A,
   A := A_ren + 2 alpha omega(K+1),   A_ren := (-1)^(K+1) a(K) + (-1)^M a(M)    [sum_{y=K+2}^{2K+2} (-1)^y b(y) = 2 alpha omega(K+1)].
 (alpha = 0: this is WHY D_ren fails near the top: A_ren != 0 while Gamma sigma(n) ~ Gamma/n^2 -> 0.)

## 5. Case (E): K >= 2, n >= 2K+2, 1 <= lo <= hi = n-1-K.
 alpha* := -A_ren / (2 omega(K+1)) = (a(K) - (-1)^(K+M) a(M)) / (2 w(K)).   (Makes A = 0.)
LEMMA 5.1.  0 < alpha* <= 2/(K+1).   [F1, F2: a(K) > a(M) > 0;  F4: w(K) > 0 and alpha* <= (a(K)+a(K+1))/(2w(K)) <= 2/(K+1).]
LEMMA 5.2.  For K+1 <= x <= n:  tau(x) = Phi(x) + tail(x) - [x <= M] (-1)^(x+M) a(M),
    tail(x) := sum_{j>=1} (-1)^(j-1) b(x+j) in [0, b(x+1)],  b(x+1) <= 2(K+1)alpha*/(x(x+1)) <= 4/(x(x+1)),  tail(x) = 0 (x >= 2K+2).
 Proof: A = 0 and 2K+2 <= n give e(x) = -sum_{y>x} (-1)^y b(y) - [x <= M](-1)^M a(M); b is >= 0 and nonincreasing on
 [x+1, inf) (x >= K+1), Lemma 3.1.  []
LOWER BOUNDS.  tau >= 0: tau = 0 on x <= K; for K+1 <= x <= M, tau(x) >= Phi(x) - a(M) >= Phi(K+1) - a(M)
 = 2/(K+1) - a(K) - a(M) > 2/(K+1) - 2a(K) > 0 (3.2 iii; F2; a(K) < 1/(K+1)); for x >= M+1, tau(x) >= Gamma sigma(x) > 0.
 eta >= 0: eta = tau except eta(K+1) = 2/(K+1) - alpha* >= 0 (5.1).  gamma in {0, alpha*} >= 0.  Hence all cells >= 0.
UPPER BOUNDS (eta <= tau, so it suffices: tau(x)+tau(y) <= 2 for y < x, x-y odd; tau(x) <= 2; tau(x)+alpha* <= 2 for x >= 2K+3):
 Phi <= 1 (3.2 v); tail <= 4/((K+1)(K+2)) <= 1/3; a(M) <= a(3) < 1/20: tau <= 1.39; for x >= 2K+3 (tail = 0)
 tau + alpha* <= 1.05 + 2/3.   For K+1 <= y < x, x-y odd (the a(M) terms cancel when both <= M):
  - x <= M:       tau(x)+tau(y) = 2 - K^2(sigma(x)+sigma(y)) + tail(x) + tail(y) <= 2   [tail(z) <= 4/(z(z+1)) <= K^2 sigma(z), K >= 2].
  - y <= M < x:   tau(x)+tau(y) <= Gamma sigma(M+1) + a(M) + 1 - K^2 sigma(y) + tail(x) + tail(y) <= 2 - K^2 sigma(M+1) + tail(x) <= 2
                  [3.2 vi; tail(x) <= 4/((M+1)(M+2)) <= K^2 sigma(M+1)].
  - M < y:        tau(x)+tau(y) <= 2 Gamma sigma(M+1) + 8/((M+1)(M+2)) <= 2 - 2/(M+1) + 8/((M+1)(M+2)) <= 2   (M >= 3).
 y <= K: eta(y) = 0 and tau(x) <= 2.   Case (E) done.  []

## 6. Case (D): K = 1 (hi = n-2), n >= 4, 1 <= lo <= n-2 (M in [2, n-1]), alpha = 2/7.
 By 4.1 (window [3,4], b(3) = 2alpha/3, b(4) = alpha/3):  tau(1) = 0, tau(2) = 1,
   tau(3) = 2(1+alpha)/3 (M >= 3),  tau(3) = 2alpha/3 (M = 2)    [3.2 i: sigma(2)+sigma(3) = 1/3, a(1) = sigma(2), a(2) = 4sigma(3) - 1/3];
   x >= 4:  tau(x) = 1 - sigma(x) + (-1)^x eP  (x <= M),   tau(x) = Gamma sigma(x) + (-1)^x A  (x >= M+1),
   eP := a(1) - alpha/3 = a(1) - 2/21,   A := eP + (-1)^M a(M).
 eta(2) = 1 - alpha, eta = tau elsewhere;  gamma(x) = alpha for odd x >= 5, gamma(1) = gamma(3) = 0.
 By F5, F2:  0 < eP < alpha,   0 < eP - a(3) <= A <= eP + a(2) <= alpha   (all M >= 2).  sigma(4) <= 1/15, sigma(5) <= 3/70.
 LOWER: even x >= 4: tau(x) >= 1 - 1/15 + eP > 0 (x <= M) or >= A > 0 (x > M).  Odd x >= 5, x <= M: tau >= 1 - 3/70 - 1/4 > 0.
   tau(3) >= 0.  Odd x >= 5, x > M: tau(x) >= -A >= -alpha, and its partners: eta(2) = 1-alpha (sum >= 1-2alpha > 0),
   gamma = alpha (sum >= alpha - A >= 0), even y >= 4: y > M gives Gamma(sigma(x)+sigma(y)) > 0, y <= M gives >= 14/15 - alpha > 0.
   Even x with odd partner y: tau(x) > 0 and tau(y) < 0 only for odd y > M (then x > M too: sum = Gamma(sigma(x)+sigma(y)) > 0).
 UPPER: tau <= 1 + alpha everywhere relevant (odd x: tau <= 1; tau(3) < 1 + alpha), so cells with eta(2), gamma are <= 2.
   x,y >= 4, x-y odd: both <= M: 2 - sigma(x) - sigma(y); both > M: <= 2 Gamma sigma(M+1) < 2; mixed: <= Gamma sigma(M+1) + a(M)
   + 1 - sigma(y) <= 2 (3.2 vi).  Pair (3, even x >= 4): M >= 3: tau(3)+tau(x) <= 2(1+alpha)/3 + 1 + eP = 5/3 + a(1) + alpha/3 < 2
   (F5: a(1) < 5/21; for x > M use Gamma sigma(M+1) + a(M) <= 1); M = 2: <= 2alpha/3 + 3/15 + alpha < 2.  Case (D) done.  []

## 7. Case (C): n <= 2K+1, alpha = 0 (no dipole; this is D_ren).
 Lemma 2.1/4.1 with alpha = 0: tau(x) = Phi(x) + (-1)^(x+K+1) a(K) + [x >= M+1] (-1)^(x+M) a(M), eta = tau, gamma = 0.
 K >= 2.  LOWER: x <= M: tau >= Phi(K+1) - a(K) = 2/(K+1) - 2a(K) > 0.  x >= M+1: tau >= Gamma sigma(n) - a(K) - a(K+1) >= 0,
   as Gamma >= 2K+1 and sigma(n) >= sigma(2K+1) >= 1/((2K+1)(2K+2)) give Gamma sigma(n) >= 1/(2(K+1)) (F3).
 UPPER: x-y odd: both <= M: Phi(x)+Phi(y) <= 2; mixed: <= Gamma sigma(M+1) + a(M) + 1 - K^2 sigma(y) <= 2 (3.2 vi); both > M:
   2 Gamma sigma(M+1) < 2; tau <= 1 + a(K) + a(M) < 2.
 K = 1: n <= 3 and 1 <= lo <= hi = n-2 force (n,lo,hi) = (3,1,1): (RUN) gives T = (T(0),T(1),T(2)) = (0,1,0), G = 0,
   and all 1-D conditions hold (by Lemma 4.1 also tau(3) = 3 sigma(3) - a(1) - a(2) = 0 exactly).  Case (C) done.  []

## 8. Lean notes
 Needed analysis: beta as a convergent alternating series (or via Real.log 2: beta(m+1) = (-1)^m (log 2 - h_m)),
 Lemma 3.1 (alternating series bounds), Lemma 3.3 (telescoping + 3.1), sigma = 4beta - 2/x.  F1-F6 become finitely many
 polynomial inequalities (K >= 10, coefficient positivity after K = 10 + t) plus 11 x 4 rational interval checks
 (K <= 11) -- all printed by verify_facts.py.  Everything else is finite algebra on explicit recursions.
====================================================================================================================

