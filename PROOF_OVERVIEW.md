# Proof overview: symmetrically thermalizing unitaries (STU)

Notation:
- p = (p_0 ≥ … ≥ p_{d−1}) is the Gibbs vector of τ_β, and q that of τ_{β'}, with β' ≤ β.
- STU(d) is the statement for dimension d.
- A *run* of a d×d array is a diagonal {(i, i+s)}. Run 0 consists of the "loops" (i, i).

## 1. Unconditional reduction to symmetric marginal spectra (Lean: `STU.lean`)
Local unitaries V ⊗ W and the spectral theorem reduce STU(d) to a spectral statement:

q ∈ symMarginalSpectra(p ⊗ p),

that is, some state unitarily equivalent to diag(p ⊗ p) has **both** marginals equal to diag(q). This reduction is `stu_of_mem_symMarginalSpectra`. It also uses the real Schur–Horn theorem, which is proved in `SchurHorn.lean` (Chan–Li-type induction, sorting-free hockey-stick majorisation).

## 2. Kirwan route: all d on paper; Lean conditional on Kirwan (`Construction.lean`, `Lemma5.lean`, `STU.lean`)
1. **Explicit reachable points v_k (proved for all d, in Lean).** Fix n = k+1 top levels T and tails J.
   - Relabel the tails by cyclic shifts.
   - On each cyclic diagonal D_s of T×T, apply a Schur–Horn unitary realising Bλ^{(s)}, where B = Σ_r β_r Π^r is a doubly stochastic circulant and β_r = (1/n − W_r)/P.
   - Then β_r ≥ 0 by a bin-packing bound W_r ≤ 1/n.
2. **Kirwan convexity (1984).** The set of reachable symmetric marginal spectra is convex. This is the only external input, stated as `KirwanSymmetricConvexity d`.
3. **Lemma 5 (proved, in Lean).** q ∈ conv{v_0, …, v_{d−1}}, with explicit barycentric coordinates. Their monotonicity reduces to a three-point exponential inequality.

⇒ STU(d) for every d, given Kirwan: `stu_exists`. The paper write-up is `math/kirwan_route_all_d_REPORT.md`.

## 3. Kirwan-free route (Lean: `KirwanFreeCore.lean`, `KirwanFree.lean`, `KirwanFreeU.lean`)
- **Fixed structure R_tri.** Symmetric configurations x on the d×d array whose runs are majorised by the runs λ^s_i = p_i p_{i+s} of p ⊗ p, realised by one fixed family of orthogonal matrices (LC blocks + Schur–Horn). R_tri is convex **by construction**, so no Kirwan is needed.
- **Lemma T.** q ∈ conv{w_k}, where w_k = min(p, p_k)/Z_k are the "clipped" thermal vectors. This holds for every concave increasing g with g(0) ≥ 0, via monotone secant slopes. It is used with g(x) = x^{β'/β}.
- **w_k ∈ R_tri.**
  - Decompose p ⊗ p = B ⊗ B + D with B = min(p, p_k). Here D = Σ_{m<k, M} c_m c_M (1+[M≥k])/2 · (Q_{min(m,M)} + U_{m,M}) is a nonnegative combination of symmetric Young diagrams: squares Q and crosses U.
  - *Superposition lemma:* sums of similarly ordered majorisations are majorisations.
  - *Hall identity:* explicit leftovers c_M[E²(M+1)/Z + F] ≥ 0.
  - Each cross is replaced by a **uniformisation of its arm interval [lo, hi]** inside a box [0, M] with M ≥ k.
- **Interval uniformisation** `IsIntervalUnif n lo hi u`:
  - u is symmetric, with entries in [0,1] and zero outside the n-box;
  - the run sums are Σ_i u(i,i+s) = #{a ∈ [lo,hi] : a ≥ s};
  - every row sums to ((hi+1)² − lo²)/n.

  Only these properties are used, and each interval is used separately.

⇒ `stu_exists_of_intervalUnif : (∀ n ≤ d, IntervalUnifAll n) → STU(d)`, machine-checked.

## 4. Interval uniformisations: what is proved
| interval | construction | status |
|---|---|---|
| [0, n−1] | J (all ones) | Lean, all n |
| [0, m], m ≤ n−2 (squares) | **renewal square** U^m_n. K = n−m−1, H(ℓ) = 1 − K²/((n−ℓ)(n−ℓ+1)). Reversal blocks: end blocks weight H(ℓ), interior blocks weight H(ℓ)−H(ℓ+1). Closed form U(i,j) = Ψ(\|i−j\|+1) + Ψ(m'+1), with Ψ(p) = Σ_{ℓ≥p} (−1)^{ℓ−p} H(ℓ) and m' = min(i+j+1, 2n−1−i−j) | **Lean, all n** (`Renewal.lean`) |
| [lo, n−1] | J − U^{lo−1}_n | Lean, all n |
| [lo, hi], 1 ≤ lo ≤ hi ≤ n−2 | (a) explicit **cross construction** X = θU^hi_n + (1−θ)·avg_t J[W_t] − ½U^{lo−1}_n − ½·avg_t U^{lo−1}_{hi+1}[W_t], with θ = 1 − lo²/(2(hi+1)²) and windows W_t = [t, t+hi]. Symmetry, runs, rows, X ≤ 1 and X ≥ 0 on runs ≥ lo are proved | Lean, all n; **X ≥ 0 on runs < lo (`XShortNonneg`) is the open inequality**: Lean for n ≤ 8, exact computer check for n ≤ 76 |
| same | (b) **difference + dipoles**: D_ren = U^hi − U^{lo−1} where it is valid; otherwise dipole corrections at levels hi, hi−1 with rational amplitudes. Runs, rows and symmetry are proved for all amplitudes, and the cell check reduces to a 1-D criterion | exact certificates for every interval, all n ≤ 140 (two independent implementations); amplitude files up to n = 256 |

The **Hook Decomposition Lemma** HD(n) gives all intervals at once (`intervalUnifAll_of_hookDecomposition`):
- HD(n) for n ≤ 20 and odd 21 ≤ n ≤ 39 by kernel-checked certificates;
- the Doubling Lemma HD(M) ⇒ HD(2M) and HD(2^k·m) for m ≤ 40, all in Lean;
- odd n ≤ 101 by exact certificates (two-dipole construction), outside Lean.

## 5. The remaining gap (for an unconditional all-d Lean proof)
It suffices to prove, for all n, **either** `XShortNonneg n lo hi` **or** the 1-D cell inequalities of the dipole construction with an explicit amplitude rule. Known structure:
- Where D_ren fails, it fails only near the top of the box: K_P = n−1−hi ≲ 0.74·n^{2/3} and lo ≳ 0.53n.
- The failure mechanism is a parity mode with exact amplitude Δ_K = ½ − K + 2K²·Σ_{j≥0}(−1)^j/(K+1+j), which is about 1/(2(K+1)²). It comes from the formula Ψ(p) = K²/(n−p+1) + c_par − 2K²·Σ_{q=K+1}^{n−p}(−1)^{n−p−q}/q.
- Any construction has an optimal margin Θ(1/n²) near the top (LP optimum ≈ 8.5/n² for hooks lo = hi = n−2). So a proof must be exact to second order there.

The working logs in `math/` contain all partial results, negative results and conjectures, including the WP odd-step reduction, the two-token (T/H/G) construction, the canonical-delta and two-dipole hook decompositions, and the product lemma.
