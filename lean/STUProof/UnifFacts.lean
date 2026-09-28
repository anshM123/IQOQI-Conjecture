import STUProof.IntervalUnif

/-!
# Special functions and the facts F1-F6 (P-PROOF, Section 3)

* `betaF x = ∑_{j ≥ 0} (-1)^j/(x+j)` (`x ≥ 1`), defined as the limit of the alternating series
  (Mathlib's alternating series test); `β(x) + β(x+1) = 1/x`, `0 ≤ β(x) ≤ 1/x`.
* Lemma 3.1 in recursion form (`alt_rec_bounds`, `alt_rec_bounds2`): if `f(x) + f(x+1) = c(x)`
  with `c` nonincreasing and `f → 0`, then `0 ≤ f ≤ c` (and the refined bounds).
* Lemma 3.3 ("Lemma B", `lemmaB`): `u(x) - ε(x) ≤ β(x) ≤ u(x)`.
* `σ(x) = 4β(x) - 2/x` (`sigmaF`): `σ(x) + σ(x+1) = 2/(x(x+1))`,
  `1/(x(x+1)) ≤ σ(x) ≤ (x+4)/(x(x+1)(x+2))`, `σ` decreasing (Lemma 3.2).
* `a(K) = 4K²β(K+1) + 1 - 2K` (`aF`), `ω(k) = ∑_{y=k+1}^{2k} (-1)^y k/(y(y-1))` (`omegaF`),
  `w(K) = (-1)^K ω(K+1)` (`wF`), and `ω(k) = (-1)^k (2kβ(k+1) - 1) + 2kβ(2k) - 1/2`.
* F1-F6 (`factF1`, …): with Lemma B inserted, each fact is a rational-function inequality whose
  numerator has nonnegative coefficients after the shift `K = k + 2` (F3, F4) or in `K` itself
  (F1, F2); `positivity` concludes. F5, F6 use Lemma B at `x = 2, 3, 4`.
-/

open Finset Filter Topology

noncomputable section

namespace STUProof

/-! ## Lemma 3.1 in recursion form -/

theorem alt_rec_bounds {f c : ℕ → ℝ} {x0 : ℕ} (hrec : ∀ x, x0 ≤ x → f x + f (x + 1) = c x)
    (hanti : ∀ x, x0 ≤ x → c (x + 1) ≤ c x) (hlim : Tendsto f atTop (𝓝 0)) {x : ℕ}
    (hx : x0 ≤ x) : 0 ≤ f x ∧ f x ≤ c x := by
  have hnn : ∀ y, x0 ≤ y → 0 ≤ f y := by
    intro y hy
    have hmono : Antitone (fun N : ℕ => f (y + 2 * N)) := by
      apply antitone_nat_of_succ_le
      intro N
      have h1 := hrec (y + 2 * N) (by omega)
      have h2 := hrec (y + 2 * N + 1) (by omega)
      have h3 := hanti (y + 2 * N) (by omega)
      show f (y + 2 * (N + 1)) ≤ f (y + 2 * N)
      rw [show y + 2 * (N + 1) = y + 2 * N + 1 + 1 by ring]
      linarith
    have htend : Tendsto (fun N : ℕ => f (y + 2 * N)) atTop (𝓝 0) :=
      hlim.comp (tendsto_atTop_mono (fun N => by show N ≤ y + 2 * N; omega) tendsto_id)
    have := hmono.le_of_tendsto htend 0
    simpa using this
  refine ⟨hnn x hx, ?_⟩
  have h1 := hrec x hx
  have h2 := hnn (x + 1) (by omega)
  linarith

theorem alt_rec_bounds2 {f c : ℕ → ℝ} {x0 : ℕ} (hrec : ∀ x, x0 ≤ x → f x + f (x + 1) = c x)
    (hanti : ∀ x, x0 ≤ x → c (x + 1) - c (x + 1 + 1) ≤ c x - c (x + 1))
    (hlim : Tendsto f atTop (𝓝 0)) {x : ℕ} (hx : x0 ≤ x) :
    c x / 2 ≤ f x ∧ f x ≤ c x / 2 + (c x - c (x + 1)) / 2 := by
  have hG := alt_rec_bounds (f := fun y => f y - f (y + 1)) (c := fun y => c y - c (y + 1))
    (x0 := x0) (fun y hy => by
      have h1 := hrec y hy
      have h2 := hrec (y + 1) (by omega)
      show f y - f (y + 1) + (f (y + 1) - f (y + 1 + 1)) = c y - c (y + 1)
      linarith)
    (fun y hy => hanti y hy)
    (by simpa using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))) hx
  have h1 := hrec x hx
  obtain ⟨g1, g2⟩ := hG
  constructor <;> linarith

/-! ## β -/

/-- `β(x) = ∑_{j ≥ 0} (-1)^j / (x + j)` for `x ≥ 1`. -/
def betaF (x : ℕ) : ℝ :=
  limUnder atTop (fun N => ∑ j ∈ range N, (-1 : ℝ) ^ j * (1 / ((x : ℝ) + j)))

theorem betaF_terms_anti {x : ℕ} (hx : 1 ≤ x) : Antitone (fun j : ℕ => 1 / ((x : ℝ) + j)) := by
  intro a b hab
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem betaF_tendsto {x : ℕ} (hx : 1 ≤ x) :
    Tendsto (fun N => ∑ j ∈ range N, (-1 : ℝ) ^ j * (1 / ((x : ℝ) + j))) atTop
      (𝓝 (betaF x)) := by
  have hzero : Tendsto (fun j : ℕ => 1 / ((x : ℝ) + j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨l, hl⟩ := (betaF_terms_anti hx).tendsto_alternating_series_of_tendsto_zero hzero
  exact tendsto_nhds_limUnder ⟨l, hl⟩

theorem betaF_add {x : ℕ} (hx : 1 ≤ x) : betaF x + betaF (x + 1) = 1 / (x : ℝ) := by
  have h1 := betaF_tendsto hx
  have h2 := betaF_tendsto (show 1 ≤ x + 1 by omega)
  have hshift : ∀ N, ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j * (1 / ((x : ℝ) + j)) =
      1 / (x : ℝ) - ∑ j ∈ range N, (-1 : ℝ) ^ j * (1 / (((x + 1 : ℕ) : ℝ) + j)) := by
    intro N
    rw [Finset.sum_range_succ']
    have e : ∀ j ∈ range N, (-1 : ℝ) ^ (j + 1) * (1 / ((x : ℝ) + ((j + 1 : ℕ) : ℝ))) =
        -((-1 : ℝ) ^ j * (1 / (((x + 1 : ℕ) : ℝ) + j))) := by
      intro j _
      push_cast
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
    simp only [pow_zero, one_mul, Nat.cast_zero, add_zero]
    ring
  have h3 : Tendsto (fun N => ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j * (1 / ((x : ℝ) + j))) atTop
      (𝓝 (betaF x)) := h1.comp (tendsto_add_atTop_nat 1)
  have h4 : Tendsto (fun N => ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j * (1 / ((x : ℝ) + j))) atTop
      (𝓝 (1 / (x : ℝ) - betaF (x + 1))) := by
    simp only [hshift]
    exact tendsto_const_nhds.sub h2
  have := tendsto_nhds_unique h3 h4
  linarith

theorem betaF_bounds {x : ℕ} (hx : 1 ≤ x) : 0 ≤ betaF x ∧ betaF x ≤ 1 / (x : ℝ) := by
  have hl := betaF_tendsto hx
  have h0 := (betaF_terms_anti hx).alternating_series_le_tendsto hl 0
  have h1 := (betaF_terms_anti hx).tendsto_le_alternating_series hl 0
  constructor
  · simpa using h0
  · simpa using h1

theorem betaF_tendsto_zero : Tendsto betaF atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx using (betaF_bounds hx).1
  · filter_upwards [eventually_ge_atTop 1] with x hx using (betaF_bounds hx).2

/-! ## Lemma B -/

/-- `u(x) = 1/(2x) + 1/(4x²) - 1/(8x⁴) + 1/(4x⁶)`. -/
def uB (x : ℝ) : ℝ := 1 / (2 * x) + 1 / (4 * x ^ 2) - 1 / (8 * x ^ 4) + 1 / (4 * x ^ 6)

/-- `ε(x) = (17x⁴+34x³+29x²+12x+2)/(8x⁶(x+1)⁶)`. -/
def epsB (x : ℝ) : ℝ := (17 * x ^ 4 + 34 * x ^ 3 + 29 * x ^ 2 + 12 * x + 2) / (8 * x ^ 6 * (x + 1) ^ 6)

theorem uB_add {x : ℝ} (hx : 0 < x) : uB x + uB (x + 1) - 1 / x = epsB x := by
  unfold uB epsB
  field_simp
  ring

theorem epsB_anti {x : ℝ} (hx : 0 < x) : epsB (x + 1) ≤ epsB x := by
  have e : epsB x - epsB (x + 1) =
      (17 * x ^ 4 + 68 * x ^ 3 + 100 * x ^ 2 + 64 * x + 16) / (x ^ 6 * (x + 1) * (x + 2) ^ 6) := by
    unfold epsB
    field_simp
    ring
  have : 0 ≤ (17 * x ^ 4 + 68 * x ^ 3 + 100 * x ^ 2 + 64 * x + 16) /
      (x ^ 6 * (x + 1) * (x + 2) ^ 6) := by positivity
  linarith

theorem uB_tendsto : Tendsto (fun x : ℕ => uB x) atTop (𝓝 0) := by
  have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have e : ∀ x : ℕ, uB x = (1 / (x : ℝ)) / 2 + (1 / (x : ℝ)) ^ 2 / 4 - (1 / (x : ℝ)) ^ 4 / 8 +
      (1 / (x : ℝ)) ^ 6 / 4 := by
    intro x
    unfold uB
    ring
  have h2 : Tendsto (fun x : ℕ => (1 / (x : ℝ)) / 2 + (1 / (x : ℝ)) ^ 2 / 4 -
      (1 / (x : ℝ)) ^ 4 / 8 + (1 / (x : ℝ)) ^ 6 / 4) atTop
      (𝓝 ((0 : ℝ) / 2 + 0 ^ 2 / 4 - 0 ^ 4 / 8 + 0 ^ 6 / 4)) :=
    (((h.div_const 2).add ((h.pow 2).div_const 4)).sub ((h.pow 4).div_const 8)).add
      ((h.pow 6).div_const 4)
  simp only [e]
  simpa using h2

/-- **Lemma B**: `u(x) - ε(x) ≤ β(x) ≤ u(x)` for `x ≥ 1`. -/
theorem lemmaB {x : ℕ} (hx : 1 ≤ x) : uB x - epsB x ≤ betaF x ∧ betaF x ≤ uB x := by
  have h := alt_rec_bounds (f := fun y : ℕ => uB y - betaF y) (c := fun y : ℕ => epsB y) (x0 := 1)
    (fun y hy => by
      have h1 := betaF_add hy
      have h2 := uB_add (x := (y : ℝ)) (by exact_mod_cast (show 0 < y by omega))
      show uB y - betaF y + (uB ((y + 1 : ℕ) : ℝ) - betaF (y + 1)) = epsB y
      push_cast
      linarith)
    (fun y hy => by
      show epsB ((y + 1 : ℕ) : ℝ) ≤ epsB y
      push_cast
      exact epsB_anti (by exact_mod_cast (show 0 < y by omega)))
    (by simpa using uB_tendsto.sub betaF_tendsto_zero) hx
  have h1 : 0 ≤ uB x - betaF x := h.1
  have h2 : uB x - betaF x ≤ epsB x := h.2
  constructor <;> linarith

/-! ## σ -/

/-- `σ(x) = ∑_{j ≥ 1} (-1)^(j-1) 2/((x+j)(x+j-1)) = 4β(x) - 2/x`. -/
def sigmaF (x : ℕ) : ℝ := 4 * betaF x - 2 / (x : ℝ)

theorem sigmaF_add {x : ℕ} (hx : 1 ≤ x) :
    sigmaF x + sigmaF (x + 1) = 2 / ((x : ℝ) * ((x : ℝ) + 1)) := by
  unfold sigmaF
  have h := betaF_add hx
  have hx' : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  push_cast
  rw [show 4 * betaF x - 2 / (x : ℝ) + (4 * betaF (x + 1) - 2 / ((x : ℝ) + 1)) =
    4 * (betaF x + betaF (x + 1)) - 2 / (x : ℝ) - 2 / ((x : ℝ) + 1) by ring, h]
  field_simp
  ring

theorem sigmaF_tendsto_zero : Tendsto sigmaF atTop (𝓝 0) := by
  have h := (betaF_tendsto_zero.const_mul 4).sub
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2)
  simp only [mul_zero, sub_zero] at h
  refine h.congr (fun x => ?_)
  unfold sigmaF
  ring

/-- **Lemma 3.2 (ii)**: `1/(x(x+1)) ≤ σ(x) ≤ (x+4)/(x(x+1)(x+2))`. -/
theorem sigmaF_bounds {x : ℕ} (hx : 1 ≤ x) :
    1 / ((x : ℝ) * ((x : ℝ) + 1)) ≤ sigmaF x ∧
      sigmaF x ≤ ((x : ℝ) + 4) / ((x : ℝ) * ((x : ℝ) + 1) * ((x : ℝ) + 2)) := by
  have h := alt_rec_bounds2 (f := sigmaF) (c := fun y : ℕ => 2 / ((y : ℝ) * ((y : ℝ) + 1)))
    (x0 := 1) (fun y hy => sigmaF_add hy)
    (fun y hy => by
      have hy' : (1 : ℝ) ≤ y := by exact_mod_cast hy
      have hy0 : (0 : ℝ) < y := by linarith
      show 2 / (((y + 1 : ℕ) : ℝ) * (((y + 1 : ℕ) : ℝ) + 1)) -
          2 / (((y + 1 + 1 : ℕ) : ℝ) * (((y + 1 + 1 : ℕ) : ℝ) + 1)) ≤
        2 / ((y : ℝ) * ((y : ℝ) + 1)) - 2 / (((y + 1 : ℕ) : ℝ) * (((y + 1 : ℕ) : ℝ) + 1))
      push_cast
      have e1 : 2 / (((y : ℝ) + 1) * ((y : ℝ) + 1 + 1)) - 2 / (((y : ℝ) + 1 + 1) * ((y : ℝ) + 1 + 1 + 1)) =
          4 / (((y : ℝ) + 1) * ((y : ℝ) + 2) * ((y : ℝ) + 3)) := by
        field_simp
        ring
      have e2 : 2 / ((y : ℝ) * ((y : ℝ) + 1)) - 2 / (((y : ℝ) + 1) * ((y : ℝ) + 1 + 1)) =
          4 / ((y : ℝ) * ((y : ℝ) + 1) * ((y : ℝ) + 2)) := by
        field_simp
        ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith)
    sigmaF_tendsto_zero hx
  have h1 : 2 / ((x : ℝ) * ((x : ℝ) + 1)) / 2 ≤ sigmaF x := h.1
  have h2 : sigmaF x ≤ 2 / ((x : ℝ) * ((x : ℝ) + 1)) / 2 +
      (2 / ((x : ℝ) * ((x : ℝ) + 1)) - 2 / (((x + 1 : ℕ) : ℝ) * (((x + 1 : ℕ) : ℝ) + 1))) / 2 := h.2
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  constructor
  · have e : 2 / ((x : ℝ) * ((x : ℝ) + 1)) / 2 = 1 / ((x : ℝ) * ((x : ℝ) + 1)) := by
      field_simp
    linarith
  · have e : 2 / ((x : ℝ) * ((x : ℝ) + 1)) / 2 +
        (2 / ((x : ℝ) * ((x : ℝ) + 1)) - 2 / (((x + 1 : ℕ) : ℝ) * (((x + 1 : ℕ) : ℝ) + 1))) / 2 =
        ((x : ℝ) + 4) / ((x : ℝ) * ((x : ℝ) + 1) * ((x : ℝ) + 2)) := by
      push_cast
      field_simp
      ring
    linarith

theorem sigmaF_pos {x : ℕ} (hx : 1 ≤ x) : 0 < sigmaF x := by
  have := (sigmaF_bounds hx).1
  have : 0 < 1 / ((x : ℝ) * ((x : ℝ) + 1)) := by
    have : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    positivity
  linarith

/-- **Lemma 3.2 (iii)**: `σ` is decreasing. -/
theorem sigmaF_succ_lt {x : ℕ} (hx : 1 ≤ x) : sigmaF (x + 1) < sigmaF x := by
  have h1 := sigmaF_add hx
  have h2 := (sigmaF_bounds (show 1 ≤ x + 1 by omega)).2
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  push_cast at h2
  have key : ((x : ℝ) + 1 + 4) / (((x : ℝ) + 1) * ((x : ℝ) + 1 + 1) * ((x : ℝ) + 1 + 2)) <
      1 / ((x : ℝ) * ((x : ℝ) + 1)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e : 2 / ((x : ℝ) * ((x : ℝ) + 1)) = 2 * (1 / ((x : ℝ) * ((x : ℝ) + 1))) := by ring
  linarith

theorem sigmaF_anti {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) : sigmaF y ≤ sigmaF x := by
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ y hxy ih => exact (sigmaF_succ_lt (by omega)).le.trans ih

/-! ## `a`, `ω`, `w` -/

/-- `a(K) = 4K²β(K+1) + 1 - 2K`. -/
def aF (K : ℕ) : ℝ := 4 * (K : ℝ) ^ 2 * betaF (K + 1) + 1 - 2 * K

theorem aF_eq_sigma (K : ℕ) : aF K = 2 / ((K : ℝ) + 1) - 1 + (K : ℝ) ^ 2 * sigmaF (K + 1) := by
  unfold aF sigmaF
  push_cast
  field_simp
  ring

/-- `ω(k) = ∑_{y=k+1}^{2k} (-1)^y k/(y(y-1))` (with `y = k+1+j`). -/
def omegaF (k : ℕ) : ℝ :=
  ∑ j ∈ range k, (-1 : ℝ) ^ (k + 1 + j) * ((k : ℝ) / (((k : ℝ) + 1 + j) * ((k : ℝ) + j)))

/-- `w(K) = (-1)^K ω(K+1)`. -/
def wF (K : ℕ) : ℝ := (-1 : ℝ) ^ K * omegaF (K + 1)

theorem alt_telescope {a : ℕ} (ha : 1 ≤ a) : ∀ L, ∑ j ∈ range L, (-1 : ℝ) ^ (a + j) / ((a : ℝ) + j) =
    (-1) ^ a * betaF a - (-1) ^ (a + L) * betaF (a + L) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have h := betaF_add (show 1 ≤ a + L by omega)
    push_cast at h
    have e : (-1 : ℝ) ^ (a + L) / ((a : ℝ) + (L : ℝ)) =
        (-1) ^ (a + L) * (betaF (a + L) + betaF (a + L + 1)) := by
      rw [h]
      ring
    rw [e, show a + (L + 1) = a + L + 1 from rfl, pow_succ]
    ring

/-- The `ω` identity: `ω(k) = (-1)^k (2kβ(k+1) - 1) + 2kβ(2k) - 1/2`. -/
theorem omegaF_eq {k : ℕ} (hk : 1 ≤ k) :
    omegaF k = (-1) ^ k * (2 * k * betaF (k + 1) - 1) + 2 * k * betaF (2 * k) - 1 / 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsplit : omegaF k = -(k : ℝ) * (∑ j ∈ range k, (-1 : ℝ) ^ (k + j) / ((k : ℝ) + j) +
      ∑ j ∈ range k, (-1 : ℝ) ^ (k + 1 + j) / (((k + 1 : ℕ) : ℝ) + j)) := by
    unfold omegaF
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hkj : (0 : ℝ) < (k : ℝ) + j := by linarith
    push_cast
    rw [show k + 1 + j = k + j + 1 by ring, pow_succ]
    field_simp
    ring
  have hT1 := alt_telescope (show 1 ≤ k by omega) k
  have hT2 := alt_telescope (show 1 ≤ k + 1 by omega) k
  have hb1 := betaF_add hk
  have hb2 := betaF_add (show 1 ≤ 2 * k by omega)
  rw [show k + k = 2 * k by ring] at hT1
  rw [show k + 1 + k = 2 * k + 1 by ring] at hT2
  have p1 : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; simp
  have p2 : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, p1]; ring
  have p3 : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  rw [hsplit, hT1, hT2, p1, p2, p3]
  have e1 : betaF k = 1 / (k : ℝ) - betaF (k + 1) := by linarith
  have e2 : betaF (2 * k + 1) = 1 / (2 * (k : ℝ)) - betaF (2 * k) := by
    push_cast at hb2
    linarith
  rw [e1, e2]
  field_simp
  ring

/-! ## The facts F1-F6 -/

/-- Upper bound of `a(K)` from Lemma B. -/
def aUp (K : ℕ) : ℝ := 4 * (K : ℝ) ^ 2 * uB ((K : ℝ) + 1) + 1 - 2 * K

/-- Lower bound of `a(K)` from Lemma B. -/
def aLo (K : ℕ) : ℝ := 4 * (K : ℝ) ^ 2 * (uB ((K : ℝ) + 1) - epsB ((K : ℝ) + 1)) + 1 - 2 * K

theorem aF_le_aUp (K : ℕ) : aF K ≤ aUp K := by
  have h := (lemmaB (show 1 ≤ K + 1 by omega)).2
  push_cast at h
  unfold aF aUp
  have : 4 * (K : ℝ) ^ 2 * betaF (K + 1) ≤ 4 * (K : ℝ) ^ 2 * uB ((K : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  linarith

theorem aLo_le_aF (K : ℕ) : aLo K ≤ aF K := by
  have h := (lemmaB (show 1 ≤ K + 1 by omega)).1
  push_cast at h
  unfold aF aLo
  have : 4 * (K : ℝ) ^ 2 * (uB ((K : ℝ) + 1) - epsB ((K : ℝ) + 1)) ≤ 4 * (K : ℝ) ^ 2 * betaF (K + 1) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  linarith

/-- Lower bound of `w(K)` for odd `K`. -/
def wOddLo (K : ℕ) : ℝ := 3 / 2 - 2 * ((K : ℝ) + 1) * (uB ((K : ℝ) + 2) + uB (2 * (K : ℝ) + 2))

/-- Lower bound of `w(K)` for even `K`. -/
def wEvenLo (K : ℕ) : ℝ := 1 / 2 - 2 * ((K : ℝ) + 1) * uB ((K : ℝ) + 2) +
  2 * ((K : ℝ) + 1) * (uB (2 * (K : ℝ) + 2) - epsB (2 * (K : ℝ) + 2))

theorem poly_F1 (K : ℕ) : aLo K = ((K : ℝ) ^ 5 + 13 * (K : ℝ) ^ 4 + 70 * (K : ℝ) ^ 3 +
    194 * (K : ℝ) ^ 2 + 256 * (K : ℝ) + 128) / (2 * ((K : ℝ) + 1) * ((K : ℝ) + 2) ^ 6) := by
  unfold aLo uB epsB
  field_simp
  ring

theorem poly_F2 (K : ℕ) : aLo K - aUp (K + 1) = (2 * (K : ℝ) ^ 4 + 23 * (K : ℝ) ^ 3 +
    101 * (K : ℝ) ^ 2 + 170 * (K : ℝ) + 98) / (2 * ((K : ℝ) + 1) * ((K : ℝ) + 2) ^ 6) := by
  unfold aLo aUp uB epsB
  push_cast
  field_simp
  ring

theorem poly_F3 (k : ℕ) : 1 / (2 * (((k + 2 : ℕ) : ℝ) + 1)) - aUp (k + 2) - aUp (k + 2 + 1) =
    ((k : ℝ) ^ 12 + 41 * (k : ℝ) ^ 11 + 764 * (k : ℝ) ^ 10 + 8545 * (k : ℝ) ^ 9 +
      63789 * (k : ℝ) ^ 8 + 334153 * (k : ℝ) ^ 7 + 1256064 * (k : ℝ) ^ 6 +
      3400638 * (k : ℝ) ^ 5 + 6544384 * (k : ℝ) ^ 4 + 8654345 * (k : ℝ) ^ 3 +
      7354236 * (k : ℝ) ^ 2 + 3503150 * (k : ℝ) + 660280) /
      (2 * ((k : ℝ) + 3) ^ 6 * ((k : ℝ) + 4) ^ 7) := by
  unfold aUp uB
  push_cast
  field_simp
  ring

theorem poly_F4a (K : ℕ) : wOddLo K = (48 * (K : ℝ) ^ 10 + 768 * (K : ℝ) ^ 9 + 5442 * (K : ℝ) ^ 8 +
    22428 * (K : ℝ) ^ 7 + 59385 * (K : ℝ) ^ 6 + 105468 * (K : ℝ) ^ 5 + 127292 * (K : ℝ) ^ 4 +
    103200 * (K : ℝ) ^ 3 + 53840 * (K : ℝ) ^ 2 + 16320 * (K : ℝ) + 2176) /
    (128 * ((K : ℝ) + 1) ^ 5 * ((K : ℝ) + 2) ^ 6) := by
  unfold wOddLo uB
  field_simp
  ring

theorem poly_F4b (k : ℕ) : 4 * wOddLo (k + 2) / (((k + 2 : ℕ) : ℝ) + 1) - aUp (k + 2) -
    aUp (k + 2 + 1) =
    (16 * (k : ℝ) ^ 10 + 544 * (k : ℝ) ^ 9 + 8242 * (k : ℝ) ^ 8 + 73212 * (k : ℝ) ^ 7 +
      421633 * (k : ℝ) ^ 6 + 1641880 * (k : ℝ) ^ 5 + 4368048 * (k : ℝ) ^ 4 +
      7817152 * (k : ℝ) ^ 3 + 8974576 * (k : ℝ) ^ 2 + 5940736 * (k : ℝ) + 1710240) /
      (32 * ((k : ℝ) + 3) ^ 6 * ((k : ℝ) + 4) ^ 6) := by
  unfold wOddLo aUp uB
  push_cast
  field_simp
  ring

theorem poly_F4c (K : ℕ) : wEvenLo K = (160 * (K : ℝ) ^ 11 + 3200 * (K : ℝ) ^ 10 +
    29012 * (K : ℝ) ^ 9 + 157296 * (K : ℝ) ^ 8 + 566317 * (K : ℝ) ^ 7 + 1420999 * (K : ℝ) ^ 6 +
    2535030 * (K : ℝ) ^ 5 + 3215114 * (K : ℝ) ^ 4 + 2841125 * (K : ℝ) ^ 3 +
    1666285 * (K : ℝ) ^ 2 + 583870 * (K : ℝ) + 92626) /
    (4 * ((K : ℝ) + 2) ^ 6 * (2 * (K : ℝ) + 3) ^ 6) := by
  unfold wEvenLo uB epsB
  field_simp
  ring

theorem poly_F4d (k : ℕ) : 4 * wEvenLo (k + 2) / (((k + 2 : ℕ) : ℝ) + 1) - aUp (k + 2) -
    aUp (k + 2 + 1) =
    (192 * (k : ℝ) ^ 16 + 10816 * (k : ℝ) ^ 15 + 285192 * (k : ℝ) ^ 14 + 4672168 * (k : ℝ) ^ 13 +
      53227666 * (k : ℝ) ^ 12 + 447135728 * (k : ℝ) ^ 11 + 2864967224 * (k : ℝ) ^ 10 +
      14282437922 * (k : ℝ) ^ 9 + 55985185735 * (k : ℝ) ^ 8 + 173131057544 * (k : ℝ) ^ 7 +
      420984335806 * (k : ℝ) ^ 6 + 796458028404 * (k : ℝ) ^ 5 + 1149337523504 * (k : ℝ) ^ 4 +
      1223024950168 * (k : ℝ) ^ 3 + 905103455591 * (k : ℝ) ^ 2 + 416231111464 * (k : ℝ) +
      89613810730) /
      (2 * ((k : ℝ) + 3) ^ 6 * ((k : ℝ) + 4) ^ 6 * (2 * (k : ℝ) + 7) ^ 6) := by
  unfold wEvenLo aUp uB epsB
  push_cast
  field_simp
  ring

/-- **F1**: `a(K) > 0`. -/
theorem factF1 (K : ℕ) : 0 < aF K := by
  have h := aLo_le_aF K
  rw [poly_F1] at h
  have : 0 < ((K : ℝ) ^ 5 + 13 * (K : ℝ) ^ 4 + 70 * (K : ℝ) ^ 3 + 194 * (K : ℝ) ^ 2 +
    256 * (K : ℝ) + 128) / (2 * ((K : ℝ) + 1) * ((K : ℝ) + 2) ^ 6) := by positivity
  linarith

/-- **F2**: `a(K+1) < a(K)`. -/
theorem factF2 (K : ℕ) : aF (K + 1) < aF K := by
  have h1 := aLo_le_aF K
  have h2 := aF_le_aUp (K + 1)
  have e := poly_F2 K
  have : 0 < (2 * (K : ℝ) ^ 4 + 23 * (K : ℝ) ^ 3 + 101 * (K : ℝ) ^ 2 + 170 * (K : ℝ) + 98) /
    (2 * ((K : ℝ) + 1) * ((K : ℝ) + 2) ^ 6) := by positivity
  linarith

theorem aF_anti {K L : ℕ} (h : K ≤ L) : aF L ≤ aF K := by
  induction L, h using Nat.le_induction with
  | base => exact le_rfl
  | succ L _ ih => exact (factF2 L).le.trans ih

/-- **F3**: `a(K) + a(K+1) ≤ 1/(2(K+1))` for `K ≥ 2`. -/
theorem factF3 {K : ℕ} (hK : 2 ≤ K) : aF K + aF (K + 1) ≤ 1 / (2 * ((K : ℝ) + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  have e := poly_F3 k
  have h1 := aF_le_aUp (k + 2)
  have h2 := aF_le_aUp (k + 2 + 1)
  have : 0 ≤ ((k : ℝ) ^ 12 + 41 * (k : ℝ) ^ 11 + 764 * (k : ℝ) ^ 10 + 8545 * (k : ℝ) ^ 9 +
      63789 * (k : ℝ) ^ 8 + 334153 * (k : ℝ) ^ 7 + 1256064 * (k : ℝ) ^ 6 +
      3400638 * (k : ℝ) ^ 5 + 6544384 * (k : ℝ) ^ 4 + 8654345 * (k : ℝ) ^ 3 +
      7354236 * (k : ℝ) ^ 2 + 3503150 * (k : ℝ) + 660280) /
      (2 * ((k : ℝ) + 3) ^ 6 * ((k : ℝ) + 4) ^ 7) := by positivity
  linarith

/-- `w(K)` in terms of `β`. -/
theorem wF_eq (K : ℕ) : wF K = -(2 * ((K : ℝ) + 1) * betaF (K + 2) - 1) +
    (-1) ^ K * (2 * ((K : ℝ) + 1) * betaF (2 * K + 2) - 1 / 2) := by
  unfold wF
  rw [omegaF_eq (show 1 ≤ K + 1 by omega), show K + 1 + 1 = K + 2 from rfl,
    show 2 * (K + 1) = 2 * K + 2 by ring]
  have p : (-1 : ℝ) ^ K * (-1) ^ (K + 1) = -1 := by
    rw [← pow_add, show K + (K + 1) = 2 * K + 1 by ring, pow_succ, pow_mul]
    simp
  push_cast
  linear_combination (2 * ((K : ℝ) + 1) * betaF (K + 2) - 1) * p

/-- **F4**: `w(K) > 0` and `(K+1)(a(K) + a(K+1)) ≤ 4 w(K)` for `K ≥ 2`. -/
theorem factF4 {K : ℕ} (hK : 2 ≤ K) :
    0 < wF K ∧ ((K : ℝ) + 1) * (aF K + aF (K + 1)) ≤ 4 * wF K := by
  have hb1 := lemmaB (show 1 ≤ K + 2 by omega)
  have hb2 := lemmaB (show 1 ≤ 2 * K + 2 by omega)
  push_cast at hb1 hb2
  have hw := wF_eq K
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have ha1 := aF_le_aUp K
  have ha2 := aF_le_aUp (K + 1)
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  rcases Nat.even_or_odd (k + 2) with hev | hod
  · have hp : (-1 : ℝ) ^ (k + 2) = 1 := hev.neg_one_pow
    rw [hp] at hw
    have hlo : wEvenLo (k + 2) ≤ wF (k + 2) := by
      unfold wEvenLo
      rw [hw]
      push_cast at hb1 hb2 ⊢
      have t1 : 2 * ((k : ℝ) + 2 + 1) * betaF (k + 2 + 2) ≤ 2 * ((k : ℝ) + 2 + 1) * uB ((k : ℝ) + 2 + 2) :=
        mul_le_mul_of_nonneg_left hb1.2 (by positivity)
      have t2 : 2 * ((k : ℝ) + 2 + 1) * (uB (2 * ((k : ℝ) + 2) + 2) - epsB (2 * ((k : ℝ) + 2) + 2)) ≤
          2 * ((k : ℝ) + 2 + 1) * betaF (2 * (k + 2) + 2) :=
        mul_le_mul_of_nonneg_left hb2.1 (by positivity)
      linarith
    have hpos : 0 < wEvenLo (k + 2) := by
      rw [poly_F4c]
      positivity
    have e := poly_F4d k
    have hnum : 0 ≤ (192 * (k : ℝ) ^ 16 + 10816 * (k : ℝ) ^ 15 + 285192 * (k : ℝ) ^ 14 +
        4672168 * (k : ℝ) ^ 13 + 53227666 * (k : ℝ) ^ 12 + 447135728 * (k : ℝ) ^ 11 +
        2864967224 * (k : ℝ) ^ 10 + 14282437922 * (k : ℝ) ^ 9 + 55985185735 * (k : ℝ) ^ 8 +
        173131057544 * (k : ℝ) ^ 7 + 420984335806 * (k : ℝ) ^ 6 + 796458028404 * (k : ℝ) ^ 5 +
        1149337523504 * (k : ℝ) ^ 4 + 1223024950168 * (k : ℝ) ^ 3 + 905103455591 * (k : ℝ) ^ 2 +
        416231111464 * (k : ℝ) + 89613810730) /
        (2 * ((k : ℝ) + 3) ^ 6 * ((k : ℝ) + 4) ^ 6 * (2 * (k : ℝ) + 7) ^ 6) := by positivity
    refine ⟨lt_of_lt_of_le hpos hlo, ?_⟩
    have h3 : aUp (k + 2) + aUp (k + 2 + 1) ≤ 4 * wEvenLo (k + 2) / (((k + 2 : ℕ) : ℝ) + 1) := by
      linarith
    have h4 : ((((k + 2 : ℕ) : ℝ)) + 1) * (aUp (k + 2) + aUp (k + 2 + 1)) ≤ 4 * wEvenLo (k + 2) := by
      rw [le_div_iff₀ hK1] at h3
      linarith
    have h5 := mul_le_mul_of_nonneg_left (add_le_add ha1 ha2) hK1.le
    linarith
  · have hp : (-1 : ℝ) ^ (k + 2) = -1 := hod.neg_one_pow
    rw [hp] at hw
    have hlo : wOddLo (k + 2) ≤ wF (k + 2) := by
      unfold wOddLo
      rw [hw]
      push_cast at hb1 hb2 ⊢
      have t1 : 2 * ((k : ℝ) + 2 + 1) * betaF (k + 2 + 2) ≤ 2 * ((k : ℝ) + 2 + 1) * uB ((k : ℝ) + 2 + 2) :=
        mul_le_mul_of_nonneg_left hb1.2 (by positivity)
      have t2 : 2 * ((k : ℝ) + 2 + 1) * betaF (2 * (k + 2) + 2) ≤
          2 * ((k : ℝ) + 2 + 1) * uB (2 * ((k : ℝ) + 2) + 2) :=
        mul_le_mul_of_nonneg_left hb2.2 (by positivity)
      linarith
    have hpos : 0 < wOddLo (k + 2) := by
      rw [poly_F4a]
      positivity
    have e := poly_F4b k
    have hnum : 0 ≤ (16 * (k : ℝ) ^ 10 + 544 * (k : ℝ) ^ 9 + 8242 * (k : ℝ) ^ 8 +
        73212 * (k : ℝ) ^ 7 + 421633 * (k : ℝ) ^ 6 + 1641880 * (k : ℝ) ^ 5 +
        4368048 * (k : ℝ) ^ 4 + 7817152 * (k : ℝ) ^ 3 + 8974576 * (k : ℝ) ^ 2 +
        5940736 * (k : ℝ) + 1710240) / (32 * ((k : ℝ) + 3) ^ 6 * ((k : ℝ) + 4) ^ 6) := by
      positivity
    refine ⟨lt_of_lt_of_le hpos hlo, ?_⟩
    have h3 : aUp (k + 2) + aUp (k + 2 + 1) ≤ 4 * wOddLo (k + 2) / (((k + 2 : ℕ) : ℝ) + 1) := by
      linarith
    have h4 : ((((k + 2 : ℕ) : ℝ)) + 1) * (aUp (k + 2) + aUp (k + 2 + 1)) ≤ 4 * wOddLo (k + 2) := by
      rw [le_div_iff₀ hK1] at h3
      linarith
    have h5 := mul_le_mul_of_nonneg_left (add_le_add ha1 ha2) hK1.le
    linarith

/-- `a(1) = 4β(2) - 1`, `a(2) = 16β(3) - 3`, `a(3) = 36β(4) - 5` enclosures (Lemma B). -/
theorem aF_one_bounds : 0.227 < aF 1 ∧ aF 1 < 0.2344 := by
  have h := lemmaB (show 1 ≤ 2 by norm_num)
  unfold aF
  norm_num [uB, epsB] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem aF_two_bounds : 0.0901 < aF 2 ∧ aF 2 < 0.092 := by
  have h := lemmaB (show 1 ≤ 3 by norm_num)
  unfold aF
  norm_num [uB, epsB] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem aF_three_bounds : 0.0466 < aF 3 ∧ aF 3 < 0.0472 := by
  have h := lemmaB (show 1 ≤ 4 by norm_num)
  unfold aF
  norm_num [uB, epsB] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **F5**: the constants of case (D) (`α = 2/7`). -/
theorem factF5 : 0 < aF 1 - 2 / 21 - aF 3 ∧ aF 1 - 2 / 21 + aF 2 ≤ 2 / 7 ∧ aF 1 < 5 / 21 := by
  obtain ⟨a1, a1'⟩ := aF_one_bounds
  obtain ⟨a2, a2'⟩ := aF_two_bounds
  obtain ⟨a3, a3'⟩ := aF_three_bounds
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **F6**: `a(1) < 1/4`, `a(3) < 1/20`. -/
theorem factF6 : aF 1 < 1 / 4 ∧ aF 3 < 1 / 20 := by
  obtain ⟨a1, a1'⟩ := aF_one_bounds
  obtain ⟨a3, a3'⟩ := aF_three_bounds
  exact ⟨by linarith, by linarith⟩

end STUProof
