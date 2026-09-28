import STUProof.DipoleUnif
import STUProof.UnifFacts
import STUProof.Renewal

/-!
# Interval uniformisations of every interval of every box

P-PROOF (`iqoqi/programs/proof/LOG.md`, "THE PROOF", Sections 4-7). For `1 ≤ lo ≤ hi ≤ n-2` put
`K = n-1-hi`, `M = n-lo`; `τ = dipTau K M α` (`STUProof/DipoleUnif.lean`). With
`Φ(x) = 1 - K²σ(x)` (`x ≤ M`), `Φ(x) = (M²-K²)σ(x)` (`x > M`) and the alternating part
`s = τ - Φ` we have `s(K+1) = a(K)` and `s(x+1) = -s(x) + b(x+1) - [x = M] a(M)`
(`dipS_base`, `dipS_succ`; this is Lemma 4.1 in recursive form). The cell conditions of
`isIntervalUnif_dip` are proved in the three cases
* (C) `n ≤ 2K+1`, `α = 0`;
* (D) `K = 1`, `n ≥ 4`, `α = 2/7`;
* (E) `K ≥ 2`, `n ≥ 2K+2`, `α = α* = (a(K) - (-1)^(K+M) a(M))/(2 w(K))`;
using only the facts F1-F6 (`STUProof/UnifFacts.lean`). Together with the renewal squares
(`lo = 0`), `J` and the complements (`hi = n-1`) this gives `intervalUnifAll_all`.
-/

open Finset

noncomputable section

namespace STUProof

/-! ## Signs -/

theorem neg_one_pow_of_odd_sub {x y : ℕ} (hyx : y < x) (h : (x - y) % 2 = 1) (c : ℕ) :
    (-1 : ℝ) ^ (x + c) = -(-1) ^ (y + c) := by
  obtain ⟨t, rfl⟩ : ∃ t, x = y + 2 * t + 1 := ⟨(x - y) / 2, by omega⟩
  rw [show y + 2 * t + 1 + c = (y + c) + 2 * t + 1 by ring, pow_succ, pow_add, pow_mul]
  simp

theorem neg_one_pow_bound {a : ℝ} (ha : 0 ≤ a) (x : ℕ) :
    -a ≤ (-1 : ℝ) ^ x * a ∧ (-1 : ℝ) ^ x * a ≤ a := by
  rcases neg_one_pow_eq_or ℝ x with h | h <;> rw [h] <;> constructor <;> linarith

theorem pow_neg_one_succ_add (a b : ℕ) : (-1 : ℝ) ^ (a + 1 + b) = -(-1) ^ (a + b) := by
  rw [show a + 1 + b = a + b + 1 by ring, pow_succ]
  ring

/-! ## The alternating part of `τ` -/

/-- The window `2(K+1)α [K+2 ≤ x ≤ 2K+2]` of `Q`. -/
def dipW (K : ℕ) (α : ℝ) (x : ℕ) : ℝ :=
  if K + 2 ≤ x ∧ x ≤ 2 * K + 2 then 2 * ((K : ℝ) + 1) * α else 0

/-- `b(y) = W(y)/(y(y-1))`. -/
def dipB (K : ℕ) (α : ℝ) (y : ℕ) : ℝ := dipW K α y / ((y : ℝ) * ((y : ℝ) - 1))

/-- The smooth part `Φ`. -/
def dipPhi (K M x : ℕ) : ℝ :=
  if x ≤ M then 1 - (K : ℝ) ^ 2 * sigmaF x else ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF x

/-- The alternating part `s = τ - Φ`. -/
def dipS (K M : ℕ) (α : ℝ) (x : ℕ) : ℝ := dipTau K M α x - dipPhi K M x

section Tau

variable {K M : ℕ} {α : ℝ}

theorem dipTau_low (hKM : K + 1 ≤ M) : ∀ x, x ≤ K → dipTau K M α x = 0 := by
  intro x
  induction x with
  | zero => intro _; rfl
  | succ x ih =>
    intro hx
    rw [dipTau, ih (by omega)]
    have hQ : dipQ K M α (x + 1) = 0 := by
      unfold dipQ qPart
      rw [if_neg (show ¬ (K + 1 ≤ x + 1) by omega), if_neg (show ¬ (M + 1 ≤ x + 1) by omega),
        if_neg (show ¬ (K + 2 ≤ x + 1 ∧ x + 1 ≤ 2 * K + 2) by omega)]
      ring
    rw [hQ]
    ring

theorem dipQ_eq {x : ℕ} (hx : K + 1 ≤ x) :
    dipQ K M α x = (if x ≤ M then 2 * (x : ℝ) * ((x : ℝ) - 1) - 2 * (K : ℝ) ^ 2
      else 2 * (M : ℝ) ^ 2 - 2 * (K : ℝ) ^ 2) + dipW K α x := by
  unfold dipQ qPart dipW
  rw [if_pos hx]
  by_cases h : x ≤ M
  · rw [if_neg (show ¬ (M + 1 ≤ x) by omega), if_pos h]
    ring
  · rw [if_pos (show M + 1 ≤ x by omega), if_neg h]
    ring

theorem dipTau_eq (x : ℕ) : dipTau K M α x = dipPhi K M x + dipS K M α x := by
  unfold dipS
  ring

theorem dipPhi_low {x : ℕ} (h : x ≤ M) : dipPhi K M x = 1 - (K : ℝ) ^ 2 * sigmaF x := by
  unfold dipPhi
  rw [if_pos h]

theorem dipPhi_high {x : ℕ} (h : M + 1 ≤ x) :
    dipPhi K M x = ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF x := by
  unfold dipPhi
  rw [if_neg (by omega)]

theorem dipTau_base (hK : 1 ≤ K) (hKM : K + 1 ≤ M) : dipTau K M α (K + 1) = 2 / ((K : ℝ) + 1) := by
  rw [dipTau, dipTau_low hKM K le_rfl, dipQ_eq le_rfl, if_pos hKM]
  unfold dipW
  rw [if_neg (show ¬ (K + 2 ≤ K + 1 ∧ K + 1 ≤ 2 * K + 2) by omega)]
  have hK' : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  push_cast
  field_simp
  ring

theorem dipS_base (hK : 1 ≤ K) (hKM : K + 1 ≤ M) : dipS K M α (K + 1) = aF K := by
  unfold dipS
  rw [dipTau_base hK hKM, dipPhi_low hKM, aF_eq_sigma]
  ring

/-- **Lemma 4.1** (recursive form). -/
theorem dipS_succ (hK : 1 ≤ K) {x : ℕ} (hx : K + 1 ≤ x) :
    dipS K M α (x + 1) = -dipS K M α x + dipB K α (x + 1) - (if x = M then aF M else 0) := by
  have hpair := dipTau_pair K M α x
  have hQ := dipQ_eq (K := K) (M := M) (α := α) (show K + 1 ≤ x + 1 by omega)
  have hsig := sigmaF_add (show 1 ≤ x by omega)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have e1 : dipTau K M α (x + 1) = dipQ K M α (x + 1) / (((x : ℝ) + 1) * x) - dipTau K M α x := by
    linarith
  have e2 : sigmaF (x + 1) = 2 / ((x : ℝ) * ((x : ℝ) + 1)) - sigmaF x := by linarith
  unfold dipS dipB
  rw [e1, hQ]
  push_cast
  rw [show (x : ℝ) + 1 - 1 = x by ring]
  by_cases h1 : x + 1 ≤ M
  · rw [if_pos h1, dipPhi_low h1, dipPhi_low (show x ≤ M by omega), if_neg (show ¬ (x = M) by omega),
      e2]
    field_simp
    ring
  · by_cases h2 : x = M
    · rw [if_neg h1, dipPhi_high (show M + 1 ≤ x + 1 by omega), dipPhi_low (show x ≤ M by omega),
        if_pos h2, aF_eq_sigma, ← h2, e2]
      field_simp
      ring
    · rw [if_neg h1, dipPhi_high (show M + 1 ≤ x + 1 by omega),
        dipPhi_high (show M + 1 ≤ x by omega), if_neg h2, e2]
      field_simp
      ring

theorem dipB_nonneg {α : ℝ} (hα : 0 ≤ α) {y : ℕ} (hy : 2 ≤ y) : 0 ≤ dipB K α y := by
  unfold dipB dipW
  have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hd : 0 < (y : ℝ) * ((y : ℝ) - 1) := by nlinarith
  split_ifs
  · exact div_nonneg (by positivity) hd.le
  · simp

theorem dipB_zero_of_gt {y : ℕ} (hy : 2 * K + 2 < y) : dipB K α y = 0 := by
  unfold dipB dipW
  rw [if_neg (by omega)]
  simp

theorem dipB_zero_alpha (y : ℕ) : dipB K 0 y = 0 := by
  unfold dipB dipW
  simp

end Tau

/-! ## `σ` consequences (Lemma 3.2 (iv)-(vi)) -/

theorem msig_le {M : ℕ} (hM : 1 ≤ M) :
    (M : ℝ) ^ 2 * sigmaF (M + 1) ≤ 1 - 1 / ((M : ℝ) + 1) := by
  have h := (sigmaF_bounds (show 1 ≤ M + 1 by omega)).2
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  push_cast at h
  have h2 : (M : ℝ) ^ 2 * (((M : ℝ) + 1 + 4) / (((M : ℝ) + 1) * ((M : ℝ) + 1 + 1) * ((M : ℝ) + 1 + 2))) ≤
      1 - 1 / ((M : ℝ) + 1) := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity), sub_mul, one_div, inv_mul_eq_div]
    rw [show ((M : ℝ) + 1) * ((M : ℝ) + 1 + 1) * ((M : ℝ) + 1 + 2) / ((M : ℝ) + 1) =
      ((M : ℝ) + 1 + 1) * ((M : ℝ) + 1 + 2) by field_simp]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ (M : ℝ) ^ 2 by positivity)
  linarith

/-- **Lemma 3.2 (vi)**: `Γσ(M+1) + a(M) ≤ 1 - K²σ(M+1)`. -/
theorem gamma_sig_add_a {K M : ℕ} (hM : 1 ≤ M) :
    ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF (M + 1) + aF M ≤ 1 - (K : ℝ) ^ 2 * sigmaF (M + 1) := by
  have h := msig_le hM
  rw [aF_eq_sigma]
  have hM' : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have e : 2 / ((M : ℝ) + 1) = 2 * (1 / ((M : ℝ) + 1)) := by ring
  nlinarith

theorem gamma_sig_le {K M : ℕ} (hM : 1 ≤ M) (hKM : K ≤ M) {x : ℕ} (hx : M + 1 ≤ x) :
    ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF x ≤ 1 - 1 / ((M : ℝ) + 1) := by
  have h := msig_le hM
  have hs := sigmaF_anti (show 1 ≤ M + 1 by omega) hx
  have hsp := sigmaF_pos (show 1 ≤ x by omega)
  have hKM' : (K : ℝ) ≤ M := by exact_mod_cast hKM
  have hG : 0 ≤ (M : ℝ) ^ 2 - (K : ℝ) ^ 2 := by nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have h1 : ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF x ≤ ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF (M + 1) :=
    mul_le_mul_of_nonneg_left hs hG
  have h2 : ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF (M + 1) ≤ (M : ℝ) ^ 2 * sigmaF (M + 1) := by
    have := sigmaF_pos (show 1 ≤ M + 1 by omega)
    nlinarith [(sq_nonneg (K : ℝ))]
  linarith

theorem phi_low_ge {K : ℕ} (hK : 1 ≤ K) {x : ℕ} (hx : K + 1 ≤ x) :
    2 / ((K : ℝ) + 1) - aF K ≤ 1 - (K : ℝ) ^ 2 * sigmaF x := by
  have hs := sigmaF_anti (show 1 ≤ K + 1 by omega) hx
  have e := aF_eq_sigma K
  have : (K : ℝ) ^ 2 * sigmaF x ≤ (K : ℝ) ^ 2 * sigmaF (K + 1) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  linarith

theorem aF_lt_half {K : ℕ} (hK : 1 ≤ K) : aF K < 1 / (2 * ((K : ℝ) + 1)) := by
  rcases Nat.lt_or_ge K 2 with h | h
  · obtain rfl : K = 1 := by omega
    have := factF6.1
    norm_num at this ⊢
    linarith
  · have h3 := factF3 h
    have h1 := factF1 (K + 1)
    linarith

/-! ## Case (C): `n ≤ 2K+1`, no dipole -/

section CaseC

variable {K M : ℕ}

theorem dipS_C (hK : 1 ≤ K) (hKM : K + 1 ≤ M) : ∀ x, K + 1 ≤ x →
    dipS K M 0 x = (-1) ^ (x + K + 1) * aF K + (if M + 1 ≤ x then (-1) ^ (x + M) * aF M else 0) := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base =>
    rw [dipS_base hK hKM, if_neg (show ¬ (M + 1 ≤ K + 1) by omega),
      show K + 1 + K + 1 = 2 * (K + 1) by ring, pow_mul]
    simp
  | succ x hx ih =>
    rw [dipS_succ hK hx, ih, dipB_zero_alpha,
      show x + 1 + K + 1 = (x + K + 1) + 1 by ring, pow_succ (-1 : ℝ) (x + K + 1)]
    by_cases h1 : x = M
    · have p2 : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; simp
      rw [if_pos h1, if_neg (show ¬ (M + 1 ≤ x) by omega), if_pos (show M + 1 ≤ x + 1 by omega), h1,
        show M + 1 + M = 2 * M + 1 by ring, p2]
      ring
    · by_cases h2 : M + 1 ≤ x
      · rw [if_neg h1, if_pos h2, if_pos (show M + 1 ≤ x + 1 by omega),
          show x + 1 + M = (x + M) + 1 by ring, pow_succ (-1 : ℝ) (x + M)]
        ring
      · rw [if_neg h1, if_neg h2, if_neg (show ¬ (M + 1 ≤ x + 1) by omega)]
        ring

theorem caseC_bounds {n : ℕ} (hK : 2 ≤ K) (hKM : K + 1 ≤ M) (hn : n ≤ 2 * K + 1) :
    (∀ x, x ≤ n → 0 ≤ dipTau K M 0 x ∧ dipTau K M 0 x ≤ 2) ∧
    (∀ x y, K + 1 ≤ y → y < x → x ≤ n → (x - y) % 2 = 1 →
      dipTau K M 0 x + dipTau K M 0 y ≤ 2) := by
  have ha := aF_lt_half (show 1 ≤ K by omega)
  have haM : aF M ≤ aF (K + 1) := aF_anti hKM
  have haM0 := factF1 M
  have haK1 := factF1 (K + 1)
  have hF3 := factF3 hK
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hvi := gamma_sig_add_a (K := K) (show 1 ≤ M by omega)
  -- value of `τ` above `K`
  have hform : ∀ x, K + 1 ≤ x → dipTau K M 0 x = dipPhi K M x + (-1) ^ (x + K + 1) * aF K +
      (if M + 1 ≤ x then (-1) ^ (x + M) * aF M else 0) := by
    intro x hx
    rw [dipTau_eq, dipS_C (by omega) hKM x hx]
    ring
  have hlow : ∀ x, x ≤ n → 0 ≤ dipTau K M 0 x := by
    intro x hx
    by_cases hxK : x ≤ K
    · rw [dipTau_low hKM x hxK]
    rw [hform x (by omega)]
    obtain ⟨s1, s1'⟩ := neg_one_pow_bound (le_of_lt (factF1 K)) (x + K + 1)
    by_cases hxM : x ≤ M
    · rw [dipPhi_low hxM, if_neg (show ¬ (M + 1 ≤ x) by omega)]
      have := phi_low_ge (show 1 ≤ K by omega) (show K + 1 ≤ x by omega)
      have e : 2 / ((K : ℝ) + 1) = 4 * (1 / (2 * ((K : ℝ) + 1))) := by field_simp; ring
      linarith
    · rw [dipPhi_high (show M + 1 ≤ x by omega), if_pos (show M + 1 ≤ x by omega)]
      obtain ⟨s2, s2'⟩ := neg_one_pow_bound haM0.le (x + M)
      -- Γσ(x) ≥ (2K+1) σ(2K+1) ≥ 1/(2K+2)
      have hs := sigmaF_anti (show 1 ≤ x by omega) (show x ≤ 2 * K + 1 by omega)
      have hsb := (sigmaF_bounds (show 1 ≤ 2 * K + 1 by omega)).1
      have hKM' : (K : ℝ) + 1 ≤ M := by exact_mod_cast hKM
      have hG : 2 * (K : ℝ) + 1 ≤ (M : ℝ) ^ 2 - (K : ℝ) ^ 2 := by nlinarith
      have hsp := sigmaF_pos (show 1 ≤ 2 * K + 1 by omega)
      push_cast at hsb
      have h1 : (2 * (K : ℝ) + 1) * sigmaF (2 * K + 1) ≤
          ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF x := by
        have := mul_le_mul hG hs hsp.le (by linarith)
        linarith
      have h2 : 1 / (2 * ((K : ℝ) + 1)) ≤ (2 * (K : ℝ) + 1) * sigmaF (2 * K + 1) := by
        have := mul_le_mul_of_nonneg_left hsb (show (0 : ℝ) ≤ 2 * (K : ℝ) + 1 by positivity)
        have e : (2 * (K : ℝ) + 1) * (1 / ((2 * (K : ℝ) + 1) * (2 * (K : ℝ) + 1 + 1))) =
            1 / (2 * ((K : ℝ) + 1)) := by field_simp; ring
        linarith
      linarith
  have hphi1 : ∀ x, K + 1 ≤ x → dipPhi K M x ≤ 1 := by
    intro x hx
    by_cases hxM : x ≤ M
    · rw [dipPhi_low hxM]
      have := sigmaF_pos (show 1 ≤ x by omega)
      nlinarith [sq_nonneg (K : ℝ)]
    · rw [dipPhi_high (show M + 1 ≤ x by omega)]
      have := gamma_sig_le (show 1 ≤ M by omega) (show K ≤ M by omega) (show M + 1 ≤ x by omega)
      have : 0 < 1 / ((M : ℝ) + 1) := by positivity
      linarith
  refine ⟨fun x hx => ⟨hlow x hx, ?_⟩, fun x y hy hyx hxn hodd => ?_⟩
  · by_cases hxK : x ≤ K
    · rw [dipTau_low hKM x hxK]
      norm_num
    rw [hform x (by omega)]
    obtain ⟨s1, s1'⟩ := neg_one_pow_bound (le_of_lt (factF1 K)) (x + K + 1)
    obtain ⟨s2, s2'⟩ := neg_one_pow_bound haM0.le (x + M)
    have hp := hphi1 x (by omega)
    have hq : 1 / (2 * ((K : ℝ) + 1)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    split_ifs <;> linarith
  · have sK := neg_one_pow_of_odd_sub hyx hodd (K + 1)
    have sM := neg_one_pow_of_odd_sub hyx hodd M
    rw [hform x (by omega), hform y hy, show x + K + 1 = x + (K + 1) by ring,
      show y + K + 1 = y + (K + 1) by ring, sK]
    by_cases hxM : x ≤ M
    · rw [dipPhi_low hxM, dipPhi_low (show y ≤ M by omega), if_neg (show ¬ (M + 1 ≤ x) by omega),
        if_neg (show ¬ (M + 1 ≤ y) by omega)]
      have := sigmaF_pos (show 1 ≤ x by omega)
      have := sigmaF_pos (show 1 ≤ y by omega)
      nlinarith [sq_nonneg (K : ℝ)]
    · by_cases hyM : y ≤ M
      · rw [dipPhi_high (show M + 1 ≤ x by omega), dipPhi_low hyM, if_pos (show M + 1 ≤ x by omega),
          if_neg (show ¬ (M + 1 ≤ y) by omega)]
        obtain ⟨s2, s2'⟩ := neg_one_pow_bound haM0.le (x + M)
        have hg : ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF x ≤ ((M : ℝ) ^ 2 - (K : ℝ) ^ 2) * sigmaF (M + 1) := by
          have hs := sigmaF_anti (show 1 ≤ M + 1 by omega) (show M + 1 ≤ x by omega)
          have hKM' : (K : ℝ) ≤ M := by exact_mod_cast (show K ≤ M by omega)
          exact mul_le_mul_of_nonneg_left hs (by nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
        have := sigmaF_pos (show 1 ≤ y by omega)
        have := sigmaF_pos (show 1 ≤ M + 1 by omega)
        nlinarith [sq_nonneg (K : ℝ)]
      · rw [dipPhi_high (show M + 1 ≤ x by omega), dipPhi_high (show M + 1 ≤ y by omega),
          if_pos (show M + 1 ≤ x by omega), if_pos (show M + 1 ≤ y by omega), sM]
        have h1 := gamma_sig_le (show 1 ≤ M by omega) (show K ≤ M by omega) (show M + 1 ≤ x by omega)
        have h2 := gamma_sig_le (show 1 ≤ M by omega) (show K ≤ M by omega) (show M + 1 ≤ y by omega)
        have : 0 < 1 / ((M : ℝ) + 1) := by positivity
        linarith

/-- Cells of case (C) (`K ≥ 2`). -/
theorem caseC_cells {n : ℕ} (hK : 2 ≤ K) (hKM : K + 1 ≤ M) (hn : n ≤ 2 * K + 1) :
    (∀ x y, 1 ≤ y → y < x → x ≤ n → (x - y) % 2 = 1 →
      0 ≤ dipTau K M 0 x + (dipTau K M 0 y - if y = K + 1 then (0 : ℝ) else 0) ∧
        dipTau K M 0 x + (dipTau K M 0 y - if y = K + 1 then (0 : ℝ) else 0) ≤ 2) ∧
    (∀ x, 1 ≤ x → x ≤ n → x % 2 = 1 →
      0 ≤ dipTau K M 0 x + (if 2 * K + 3 ≤ x then (0 : ℝ) else 0) ∧
        dipTau K M 0 x + (if 2 * K + 3 ≤ x then (0 : ℝ) else 0) ≤ 2) := by
  obtain ⟨hb, hp⟩ := caseC_bounds hK hKM hn
  refine ⟨fun x y hy hyx hxn hodd => ?_, fun x _ hxn _ => ?_⟩
  · simp only [ite_self, sub_zero]
    obtain ⟨h1, h2⟩ := hb x hxn
    obtain ⟨h3, h4⟩ := hb y (by omega)
    refine ⟨by linarith, ?_⟩
    by_cases hyK : y ≤ K
    · rw [dipTau_low hKM y hyK]
      linarith
    · exact hp x y (by omega) hyx hxn hodd
  · simp only [ite_self, add_zero]
    exact hb x hxn

/-- The single case (C) box with `K = 1`: `(n, lo, hi) = (3, 1, 1)`. -/
theorem caseC_K1_cells :
    (∀ x y, 1 ≤ y → y < x → x ≤ 3 → (x - y) % 2 = 1 →
      0 ≤ dipTau 1 2 0 x + (dipTau 1 2 0 y - if y = 1 + 1 then (0 : ℝ) else 0) ∧
        dipTau 1 2 0 x + (dipTau 1 2 0 y - if y = 1 + 1 then (0 : ℝ) else 0) ≤ 2) ∧
    (∀ x, 1 ≤ x → x ≤ 3 → x % 2 = 1 →
      0 ≤ dipTau 1 2 0 x + (if 2 * 1 + 3 ≤ x then (0 : ℝ) else 0) ∧
        dipTau 1 2 0 x + (if 2 * 1 + 3 ≤ x then (0 : ℝ) else 0) ≤ 2) := by
  have t1 : dipTau 1 2 0 1 = 0 := by norm_num [dipTau, dipQ, qPart]
  have t2 : dipTau 1 2 0 2 = 1 := by norm_num [dipTau, dipQ, qPart]
  have t3 : dipTau 1 2 0 3 = 0 := by norm_num [dipTau, dipQ, qPart]
  refine ⟨fun x y hy hyx hxn hodd => ?_, fun x hx hxn _ => ?_⟩
  · simp only [ite_self, sub_zero]
    interval_cases x <;> interval_cases y <;> simp_all
  · simp only [ite_self, add_zero]
    interval_cases x <;> simp_all

end CaseC

/-! ## Common bounds -/

theorem dipB_le {K : ℕ} {α : ℝ} (hα2 : ((K : ℝ) + 1) * α ≤ 2) {y : ℕ} (hy : 2 ≤ y) :
    dipB K α y ≤ 4 / ((y : ℝ) * ((y : ℝ) - 1)) := by
  unfold dipB dipW
  have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hd : 0 < (y : ℝ) * ((y : ℝ) - 1) := by nlinarith
  split_ifs
  · apply div_le_div_of_nonneg_right _ hd.le
    linarith
  · rw [zero_div]
    positivity

theorem dipB_anti {K : ℕ} {α : ℝ} (hα : 0 ≤ α) {y : ℕ} (hy : K + 2 ≤ y) :
    dipB K α (y + 1) ≤ dipB K α y := by
  by_cases h : y + 1 ≤ 2 * K + 2
  · unfold dipB dipW
    rw [if_pos (show K + 2 ≤ y + 1 ∧ y + 1 ≤ 2 * K + 2 by omega),
      if_pos (show K + 2 ≤ y ∧ y ≤ 2 * K + 2 by omega)]
    have hy' : (2 : ℝ) ≤ y := by exact_mod_cast (show 2 ≤ y by omega)
    push_cast
    apply div_le_div_of_nonneg_left (by positivity) (by nlinarith) (by nlinarith)
  · rw [dipB_zero_of_gt (by omega)]
    exact dipB_nonneg hα (by omega)

/-! ## Case (E): `K ≥ 2`, `n ≥ 2K+2`, one dipole of amplitude `α*` -/

/-- The dipole amplitude of case (E): `α* = (a(K) - (-1)^(K+M) a(M)) / (2 w(K))`. -/
def alphaStar (K M : ℕ) : ℝ := (aF K - (-1) ^ (K + M) * aF M) / (2 * wF K)

/-- `tail(x) = ∑_{y > x} (-1)^(y-x-1) b(y)` (a finite sum: `b` vanishes above `2K+2`). -/
def dipTail (K : ℕ) (α : ℝ) (x : ℕ) : ℝ :=
  ∑ j ∈ range (2 * K + 2 - x), (-1 : ℝ) ^ j * dipB K α (x + 1 + j)

section CaseE

variable {K M : ℕ}

/-- **Lemma 5.1**: `0 < α* ≤ 2/(K+1)`. -/
theorem alphaStar_bounds (hK : 2 ≤ K) (hKM : K + 1 ≤ M) :
    0 < alphaStar K M ∧ alphaStar K M ≤ 2 / ((K : ℝ) + 1) := by
  obtain ⟨hw, hw4⟩ := factF4 hK
  have h1 : aF M ≤ aF (K + 1) := aF_anti hKM
  have h2 := factF2 K
  have h3 := factF1 M
  obtain ⟨s1, s2⟩ := neg_one_pow_bound h3.le (K + M)
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  unfold alphaStar
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_le_div_iff₀ (by linarith) hK1]
    have hnum : aF K - (-1) ^ (K + M) * aF M ≤ aF K + aF (K + 1) := by linarith
    have := mul_le_mul_of_nonneg_right hnum hK1.le
    nlinarith

theorem dipTail_base (α : ℝ) : dipTail K α (K + 1) = 2 * α * wF K := by
  unfold dipTail wF omegaF
  rw [show 2 * K + 2 - (K + 1) = K + 1 by omega, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  unfold dipB dipW
  rw [if_pos (show K + 2 ≤ K + 1 + 1 + j ∧ K + 1 + 1 + j ≤ 2 * K + 2 by omega)]
  have hp : (-1 : ℝ) ^ K * (-1) ^ (K + 1 + 1 + j) = (-1) ^ j := by
    rw [← pow_add, show K + (K + 1 + 1 + j) = 2 * (K + 1) + j by ring, pow_add, pow_mul]
    simp
  have hj' : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  rw [show (K : ℝ) + 1 + 1 + j - 1 = K + 1 + j by ring,
    show 2 * α * ((-1 : ℝ) ^ K * ((-1) ^ (K + 1 + 1 + j) * (((K : ℝ) + 1) /
      (((K : ℝ) + 1 + 1 + j) * ((K : ℝ) + 1 + j))))) =
      2 * α * ((-1 : ℝ) ^ K * (-1) ^ (K + 1 + 1 + j)) * (((K : ℝ) + 1) /
      (((K : ℝ) + 1 + 1 + j) * ((K : ℝ) + 1 + j))) by ring, hp]
  field_simp

theorem dipTail_succ (α : ℝ) (x : ℕ) :
    dipTail K α x = dipB K α (x + 1) - dipTail K α (x + 1) := by
  unfold dipTail
  by_cases hx : x + 1 ≤ 2 * K + 2
  · rw [show 2 * K + 2 - x = (2 * K + 2 - (x + 1)) + 1 by omega, Finset.sum_range_succ']
    have e : ∀ j ∈ range (2 * K + 2 - (x + 1)), (-1 : ℝ) ^ (j + 1) * dipB K α (x + 1 + (j + 1)) =
        -((-1 : ℝ) ^ j * dipB K α (x + 1 + 1 + j)) := by
      intro j _
      rw [pow_succ, show x + 1 + (j + 1) = x + 1 + 1 + j by ring]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
    simp only [pow_zero, one_mul, Nat.add_zero]
    ring
  · rw [show 2 * K + 2 - x = 0 by omega, show 2 * K + 2 - (x + 1) = 0 by omega,
      dipB_zero_of_gt (by omega)]
    simp

theorem dipTail_zero {α : ℝ} {x : ℕ} (hx : 2 * K + 2 ≤ x) : dipTail K α x = 0 := by
  unfold dipTail
  rw [show 2 * K + 2 - x = 0 by omega]
  simp

theorem dipTail_bounds {α : ℝ} (hα : 0 ≤ α) :
    ∀ x, K + 1 ≤ x → 0 ≤ dipTail K α x ∧ dipTail K α x ≤ dipB K α (x + 1) := by
  have main : ∀ q x, K + 1 ≤ x → 2 * K + 2 ≤ x + q →
      0 ≤ dipTail K α x ∧ dipTail K α x ≤ dipB K α (x + 1) := by
    intro q
    induction q with
    | zero =>
      intro x hx hq
      rw [dipTail_zero (by omega)]
      exact ⟨le_rfl, dipB_nonneg hα (by omega)⟩
    | succ q ih =>
      intro x hx hq
      by_cases h : 2 * K + 2 ≤ x + q
      · exact ih x hx h
      · obtain ⟨i1, i2⟩ := ih (x + 1) (by omega) (by omega)
        have e := dipTail_succ (K := K) α x
        have hb := dipB_anti (K := K) hα (show K + 2 ≤ x + 1 by omega)
        constructor <;> linarith
  intro x hx
  exact main (2 * K + 2) x hx (by omega)

theorem dipS_E (hK : 2 ≤ K) (hKM : K + 1 ≤ M) : ∀ x, K + 1 ≤ x →
    dipS K M (alphaStar K M) x =
      dipTail K (alphaStar K M) x - (if x ≤ M then (-1) ^ (x + M) * aF M else 0) := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base =>
    rw [dipS_base (by omega) hKM, dipTail_base, if_pos hKM,
      show K + 1 + M = (K + M) + 1 by ring, pow_succ]
    have hw := (factF4 hK).1
    unfold alphaStar
    field_simp
    ring
  | succ x hx ih =>
    rw [dipS_succ (by omega) hx, ih, dipTail_succ _ x]
    by_cases h1 : x = M
    · rw [if_pos h1, if_pos (show x ≤ M by omega), if_neg (show ¬ (x + 1 ≤ M) by omega), h1,
        show M + M = 2 * M by ring, pow_mul]
      simp only [even_two, Even.neg_pow, one_pow, one_mul, sub_zero]
      ring
    · by_cases h2 : x + 1 ≤ M
      · rw [if_neg h1, if_pos (show x ≤ M by omega), if_pos h2,
          show x + 1 + M = (x + M) + 1 by ring, pow_succ (-1 : ℝ) (x + M)]
        ring
      · rw [if_neg h1, if_neg (show ¬ (x ≤ M) by omega), if_neg h2]
        ring

set_option maxHeartbeats 1000000 in
/-- Cells of case (E), for any amplitude `α ∈ (0, 2/(K+1)]` with the alternating part of
Lemma 5.2. -/
theorem caseE_cells_gen {n : ℕ} {α : ℝ} (hK : 2 ≤ K) (hKM : K + 1 ≤ M)
    (hα0 : 0 < α) (hα2 : α ≤ 2 / ((K : ℝ) + 1))
    (hS : ∀ x, K + 1 ≤ x → dipS K M α x = dipTail K α x - (if x ≤ M then (-1) ^ (x + M) * aF M else 0)) :
    (∀ x y, 1 ≤ y → y < x → x ≤ n → (x - y) % 2 = 1 →
      0 ≤ dipTau K M α x + (dipTau K M α y - if y = K + 1 then α else 0) ∧
        dipTau K M α x + (dipTau K M α y - if y = K + 1 then α else 0) ≤ 2) ∧
    (∀ x, 1 ≤ x → x ≤ n → x % 2 = 1 →
      0 ≤ dipTau K M α x + (if 2 * K + 3 ≤ x then α else 0) ∧
        dipTau K M α x + (if 2 * K + 3 ≤ x then α else 0) ≤ 2) := by
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hαK : ((K : ℝ) + 1) * α ≤ 2 := by
    rw [le_div_iff₀ hK1] at hα2
    linarith
  have haK := aF_lt_half (show 1 ≤ K by omega)
  have haMK : aF M ≤ aF (K + 1) := aF_anti hKM
  have haK1 := factF2 K
  have haM0 := factF1 M
  have ha1 : aF M < 1 / 4 := lt_of_le_of_lt (aF_anti (show 1 ≤ M by omega)) factF6.1
  have hvi := gamma_sig_add_a (K := K) (show 1 ≤ M by omega)
  have htail := dipTail_bounds (K := K) hα0.le
  have hKM' : (K : ℝ) + 1 ≤ M := by exact_mod_cast hKM
  have hG : 0 ≤ (M : ℝ) ^ 2 - (K : ℝ) ^ 2 := by nlinarith
  have hform : ∀ x, K + 1 ≤ x → dipTau K M α x = dipPhi K M x + dipTail K α x -
      (if x ≤ M then (-1) ^ (x + M) * aF M else 0) := by
    intro x hx
    rw [dipTau_eq, hS x hx]
    ring
  have htail4 : ∀ x, K + 1 ≤ x → dipTail K α x ≤ 4 / (((x : ℝ) + 1) * x) := by
    intro x hx
    have h1 := (htail x hx).2
    have h2 := dipB_le (K := K) hαK (show 2 ≤ x + 1 by omega)
    push_cast at h2
    rw [show (x : ℝ) + 1 - 1 = x by ring] at h2
    linarith
  have hsigK : ∀ z : ℕ, 1 ≤ z → 4 / (((z : ℝ) + 1) * z) ≤ (K : ℝ) ^ 2 * sigmaF z := by
    intro z hz
    have hs := (sigmaF_bounds hz).1
    have hz' : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
    have e : 4 / (((z : ℝ) + 1) * z) = 4 * (1 / ((z : ℝ) * ((z : ℝ) + 1))) := by
      field_simp
    have hK4 : (4 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    rw [e]
    exact mul_le_mul hK4 hs (by positivity) (by positivity)
  have hlow : ∀ x, 0 ≤ dipTau K M α x := by
    intro x
    by_cases hxK : x ≤ K
    · rw [dipTau_low hKM x hxK]
    rw [hform x (by omega)]
    obtain ⟨t0, _⟩ := htail x (by omega)
    by_cases hxM : x ≤ M
    · rw [dipPhi_low hxM, if_pos hxM]
      obtain ⟨_, s2'⟩ := neg_one_pow_bound haM0.le (x + M)
      have := phi_low_ge (show 1 ≤ K by omega) (show K + 1 ≤ x by omega)
      have e : 2 / ((K : ℝ) + 1) = 4 * (1 / (2 * ((K : ℝ) + 1))) := by field_simp; ring
      linarith
    · rw [dipPhi_high (show M + 1 ≤ x by omega), if_neg hxM]
      have hs := sigmaF_pos (show 1 ≤ x by omega)
      have := mul_nonneg hG hs.le
      linarith
  have hphi1 : ∀ x, K + 1 ≤ x → dipPhi K M x ≤ 1 := by
    intro x hx
    by_cases hxM : x ≤ M
    · rw [dipPhi_low hxM]
      have hs := sigmaF_pos (show 1 ≤ x by omega)
      have := mul_nonneg (sq_nonneg (K : ℝ)) hs.le
      linarith
    · rw [dipPhi_high (show M + 1 ≤ x by omega)]
      have := gamma_sig_le (show 1 ≤ M by omega) (show K ≤ M by omega) (show M + 1 ≤ x by omega)
      have : 0 < 1 / ((M : ℝ) + 1) := by positivity
      linarith
  have hup : ∀ x, dipTau K M α x ≤ 1 + 1 / 3 + 1 / 4 := by
    intro x
    by_cases hxK : x ≤ K
    · rw [dipTau_low hKM x hxK]
      norm_num
    rw [hform x (by omega)]
    have t1 := htail4 x (by omega)
    have hx' : ((K : ℝ) + 1) ≤ x := by exact_mod_cast (show K + 1 ≤ x by omega)
    have hx0 : (0 : ℝ) < x := by linarith
    have t2 : 4 / (((x : ℝ) + 1) * x) ≤ 1 / 3 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hp := hphi1 x (by omega)
    obtain ⟨s1, s2⟩ := neg_one_pow_bound haM0.le (x + M)
    split_ifs <;> linarith
  have hupA : ∀ x, 2 * K + 3 ≤ x → dipTau K M α x + α ≤ 2 := by
    intro x hx
    rw [hform x (by omega), dipTail_zero (by omega)]
    have hα3 : α ≤ 2 / 3 := by
      have : 2 / ((K : ℝ) + 1) ≤ 2 / 3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      linarith
    have hp := hphi1 x (by omega)
    obtain ⟨s1, s2⟩ := neg_one_pow_bound haM0.le (x + M)
    split_ifs <;> linarith
  have hpair : ∀ x y, K + 1 ≤ y → y < x → (x - y) % 2 = 1 →
      dipTau K M α x + dipTau K M α y ≤ 2 := by
    intro x y hy hyx hodd
    have sM := neg_one_pow_of_odd_sub hyx hodd M
    rw [hform x (by omega), hform y hy]
    have tx := htail4 x (by omega)
    have ty := htail4 y hy
    have kx := hsigK x (by omega)
    have ky := hsigK y (by omega)
    by_cases hxM : x ≤ M
    · rw [dipPhi_low hxM, dipPhi_low (show y ≤ M by omega), if_pos hxM,
        if_pos (show y ≤ M by omega), sM]
      linarith
    · have hx' : ((M : ℝ) + 1) ≤ x := by exact_mod_cast (show M + 1 ≤ x by omega)
      have hx0 : (0 : ℝ) < x := by linarith
      by_cases hyM : y ≤ M
      · rw [dipPhi_high (show M + 1 ≤ x by omega), dipPhi_low hyM, if_neg hxM, if_pos hyM]
        obtain ⟨s2, s2'⟩ := neg_one_pow_bound haM0.le (y + M)
        have hs := sigmaF_anti (show 1 ≤ M + 1 by omega) (show M + 1 ≤ x by omega)
        have hg := mul_le_mul_of_nonneg_left hs hG
        have kM := hsigK (M + 1) (by omega)
        have t3 : 4 / (((x : ℝ) + 1) * x) ≤ 4 / ((((M + 1 : ℕ) : ℝ) + 1) * ((M + 1 : ℕ) : ℝ)) := by
          push_cast
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
        linarith
      · rw [dipPhi_high (show M + 1 ≤ x by omega), dipPhi_high (show M + 1 ≤ y by omega),
          if_neg hxM, if_neg hyM]
        have g1 := gamma_sig_le (show 1 ≤ M by omega) (show K ≤ M by omega) (show M + 1 ≤ x by omega)
        have g2 := gamma_sig_le (show 1 ≤ M by omega) (show K ≤ M by omega) (show M + 1 ≤ y by omega)
        have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast (show 3 ≤ M by omega)
        have hy' : ((M : ℝ) + 1) ≤ y := by exact_mod_cast (show M + 1 ≤ y by omega)
        have hy0 : (0 : ℝ) < y := by linarith
        have t3 : 4 / (((x : ℝ) + 1) * x) ≤ 1 / ((M : ℝ) + 1) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have t4 : 4 / (((y : ℝ) + 1) * y) ≤ 1 / ((M : ℝ) + 1) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  have hKK : dipTau K M α (K + 1) = 2 / ((K : ℝ) + 1) := dipTau_base (by omega) hKM
  refine ⟨fun x y hy hyx hxn hodd => ?_, fun x _ _ _ => ?_⟩
  · have lx := hlow x
    have ly := hlow y
    by_cases hyK : y = K + 1
    · subst hyK
      rw [if_pos rfl, hKK]
      have := hpair x (K + 1) le_rfl hyx hodd
      rw [hKK] at this
      constructor <;> linarith
    · rw [if_neg hyK, sub_zero]
      refine ⟨by linarith, ?_⟩
      by_cases hyK' : y ≤ K
      · rw [dipTau_low hKM y hyK']
        have := hup x
        linarith
      · exact hpair x y (by omega) hyx hodd
  · have lx := hlow x
    split_ifs with h
    · exact ⟨by linarith, hupA x h⟩
    · have := hup x
      constructor <;> linarith

/-- Cells of case (E) with `α = α*`. -/
theorem caseE_cells {n : ℕ} (hK : 2 ≤ K) (hKM : K + 1 ≤ M) :
    (∀ x y, 1 ≤ y → y < x → x ≤ n → (x - y) % 2 = 1 →
      0 ≤ dipTau K M (alphaStar K M) x +
          (dipTau K M (alphaStar K M) y - if y = K + 1 then alphaStar K M else 0) ∧
        dipTau K M (alphaStar K M) x +
          (dipTau K M (alphaStar K M) y - if y = K + 1 then alphaStar K M else 0) ≤ 2) ∧
    (∀ x, 1 ≤ x → x ≤ n → x % 2 = 1 →
      0 ≤ dipTau K M (alphaStar K M) x + (if 2 * K + 3 ≤ x then alphaStar K M else 0) ∧
        dipTau K M (alphaStar K M) x + (if 2 * K + 3 ≤ x then alphaStar K M else 0) ≤ 2) :=
  caseE_cells_gen hK hKM (alphaStar_bounds hK hKM).1 (alphaStar_bounds hK hKM).2
    (dipS_E hK hKM)

end CaseE

/-! ## Case (D): `K = 1`, `n ≥ 4`, one dipole of amplitude `2/7` -/

section CaseD

variable {M : ℕ}

theorem dipB_D3 : dipB 1 (2 / 7) 3 = 4 / 21 := by
  unfold dipB dipW
  norm_num

theorem dipB_D4 : dipB 1 (2 / 7) 4 = 2 / 21 := by
  unfold dipB dipW
  norm_num

theorem dipS_D (hM : 2 ≤ M) : ∀ x, 4 ≤ x →
    dipS 1 M (2 / 7) x = (-1) ^ x * (aF 1 - 2 / 21 + (if M + 1 ≤ x then (-1) ^ M * aF M else 0)) := by
  have s2 : dipS 1 M (2 / 7) 2 = aF 1 := dipS_base (le_refl 1) hM
  have s3 := dipS_succ (M := M) (α := 2 / 7) (le_refl 1) (show 1 + 1 ≤ 2 by omega)
  have s4 := dipS_succ (M := M) (α := 2 / 7) (le_refl 1) (show 1 + 1 ≤ 3 by omega)
  rw [s2, dipB_D3] at s3
  rw [s3, dipB_D4] at s4
  intro x hx
  induction x, hx using Nat.le_induction with
  | base =>
    rw [s4]
    by_cases h2 : M = 2
    · subst h2
      rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
      norm_num
      ring
    · by_cases h3 : M = 3
      · subst h3
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
        norm_num
        ring
      · rw [if_neg (show ¬ (2 = M) by omega), if_neg (show ¬ (3 = M) by omega),
          if_neg (show ¬ (M + 1 ≤ 4) by omega)]
        norm_num
        ring
  | succ x hx ih =>
    rw [dipS_succ (M := M) (le_refl 1) (show 1 + 1 ≤ x by omega), ih, dipB_zero_of_gt (by omega), pow_succ]
    by_cases h1 : x = M
    · rw [if_pos h1, if_neg (show ¬ (M + 1 ≤ x) by omega), if_pos (show M + 1 ≤ x + 1 by omega), h1]
      have : (-1 : ℝ) ^ M * (-1) ^ M = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
      linear_combination (aF M) * this
    · by_cases h2 : M + 1 ≤ x
      · rw [if_neg h1, if_pos h2, if_pos (show M + 1 ≤ x + 1 by omega)]
        ring
      · rw [if_neg h1, if_neg h2, if_neg (show ¬ (M + 1 ≤ x + 1) by omega)]
        ring

theorem tauD_three (hM : 2 ≤ M) :
    dipTau 1 M (2 / 7) 3 = if M = 2 then 4 / 21 else 6 / 7 := by
  have s3 := dipS_succ (M := M) (α := 2 / 7) (le_refl 1) (show 1 + 1 ≤ 2 by omega)
  rw [dipS_base (le_refl 1) hM, dipB_D3] at s3
  have hsig := sigmaF_add (show 1 ≤ 2 by omega)
  have ha1 := aF_eq_sigma 1
  have ha2 := aF_eq_sigma 2
  rw [dipTau_eq, s3]
  norm_num at hsig ha1 ha2
  by_cases h : M = 2
  · subst h
    rw [if_pos rfl, if_pos rfl, dipPhi_high (show 2 + 1 ≤ 3 by omega)]
    norm_num
    linarith
  · rw [if_neg (show ¬ (2 = M) by omega), if_neg h, dipPhi_low (show 3 ≤ M by omega)]
    norm_num
    linarith

set_option maxHeartbeats 1000000 in
theorem caseD_cells {n : ℕ} (hM : 2 ≤ M) (hMn : M + 1 ≤ n) :
    (∀ x y, 1 ≤ y → y < x → x ≤ n → (x - y) % 2 = 1 →
      0 ≤ dipTau 1 M (2 / 7) x + (dipTau 1 M (2 / 7) y - if y = 1 + 1 then (2 / 7 : ℝ) else 0) ∧
        dipTau 1 M (2 / 7) x + (dipTau 1 M (2 / 7) y - if y = 1 + 1 then (2 / 7 : ℝ) else 0) ≤ 2) ∧
    (∀ x, 1 ≤ x → x ≤ n → x % 2 = 1 →
      0 ≤ dipTau 1 M (2 / 7) x + (if 2 * 1 + 3 ≤ x then (2 / 7 : ℝ) else 0) ∧
        dipTau 1 M (2 / 7) x + (if 2 * 1 + 3 ≤ x then (2 / 7 : ℝ) else 0) ≤ 2) := by
  obtain ⟨f5a, f5b, f5c⟩ := factF5
  obtain ⟨a1lo, a1hi⟩ := aF_one_bounds
  have haM : aF M ≤ aF 2 := aF_anti hM
  have haM0 := factF1 M
  have ha2 := factF2 1
  have hvi := gamma_sig_add_a (K := 1) (show 1 ≤ M by omega)
  simp only [Nat.cast_one, one_pow, one_mul] at hvi
  have t1 : dipTau 1 M (2 / 7) 1 = 0 := dipTau_low (show 1 + 1 ≤ M by omega) 1 le_rfl
  have t2 : dipTau 1 M (2 / 7) 2 = 1 := by
    rw [dipTau_base (le_refl 1) (show 1 + 1 ≤ M by omega)]
    norm_num
  have t3 := tauD_three hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : 0 ≤ (M : ℝ) ^ 2 - 1 := by nlinarith
  -- `A = eP + (-1)^M a(M)` lies in `(0, 2/7]`, `eP = a(1) - 2/21`
  have hA : 0 < aF 1 - 2 / 21 + (-1) ^ M * aF M ∧ aF 1 - 2 / 21 + (-1) ^ M * aF M ≤ 2 / 7 := by
    rcases neg_one_pow_eq_or ℝ M with h | h
    · rw [h]
      constructor <;> linarith
    · rw [h]
      rcases Nat.lt_or_ge M 3 with h' | h'
      · have hM2 : M = 2 := by omega
        subst hM2
        norm_num at h
      · have ha3 : aF M ≤ aF 3 := aF_anti h'
        constructor <;> linarith
  obtain ⟨hA0, hA1⟩ := hA
  have hs4 : ∀ x, 4 ≤ x → sigmaF x ≤ 1 / 15 := by
    intro x hx
    have h1 := sigmaF_anti (show 1 ≤ 4 by omega) hx
    have h2 := (sigmaF_bounds (show 1 ≤ 4 by omega)).2
    norm_num at h2
    linarith
  have hs5 : ∀ x, 5 ≤ x → sigmaF x ≤ 3 / 70 := by
    intro x hx
    have h1 := sigmaF_anti (show 1 ≤ 5 by omega) hx
    have h2 := (sigmaF_bounds (show 1 ≤ 5 by omega)).2
    norm_num at h2
    linarith
  have hG : ∀ x, M + 1 ≤ x → 0 ≤ ((M : ℝ) ^ 2 - 1) * sigmaF x ∧
      ((M : ℝ) ^ 2 - 1) * sigmaF x ≤ 1 - 1 / ((M : ℝ) + 1) := by
    intro x hx
    have g := gamma_sig_le (K := 1) (show 1 ≤ M by omega) (show 1 ≤ M by omega) hx
    simp only [Nat.cast_one, one_pow] at g
    have hs := sigmaF_pos (show 1 ≤ x by omega)
    exact ⟨mul_nonneg hM1 hs.le, g⟩
  -- `Γσ(x) + A ≤ 1 + eP` for `x > M`
  have hGA : ∀ x, M + 1 ≤ x → ((M : ℝ) ^ 2 - 1) * sigmaF x + (aF 1 - 2 / 21 + (-1) ^ M * aF M) ≤
      1 + (aF 1 - 2 / 21) := by
    intro x hx
    have hs := sigmaF_anti (show 1 ≤ M + 1 by omega) hx
    have hGx := mul_le_mul_of_nonneg_left hs hM1
    have hsM := sigmaF_pos (show 1 ≤ M + 1 by omega)
    obtain ⟨_, s2⟩ := neg_one_pow_bound haM0.le M
    linarith
  have hxlow : ∀ x, 4 ≤ x → x ≤ M →
      dipTau 1 M (2 / 7) x = 1 - sigmaF x + (-1) ^ x * (aF 1 - 2 / 21) := by
    intro x hx hxM
    rw [dipTau_eq, dipS_D hM x hx, dipPhi_low hxM, if_neg (show ¬ (M + 1 ≤ x) by omega)]
    norm_num
  have hxhigh : ∀ x, M + 1 ≤ x → 4 ≤ x → dipTau 1 M (2 / 7) x =
      ((M : ℝ) ^ 2 - 1) * sigmaF x + (-1) ^ x * (aF 1 - 2 / 21 + (-1) ^ M * aF M) := by
    intro x hxM hx
    rw [dipTau_eq, dipS_D hM x hx, dipPhi_high hxM, if_pos hxM]
    norm_num
  have hbig : ∀ x, 4 ≤ x →
      (x % 2 = 0 → 0 ≤ dipTau 1 M (2 / 7) x ∧ dipTau 1 M (2 / 7) x ≤ 1 + (aF 1 - 2 / 21)) ∧
      (x % 2 = 1 → -(2 / 7) ≤ dipTau 1 M (2 / 7) x ∧ dipTau 1 M (2 / 7) x ≤ 1) := by
    intro x hx
    have hsx := hs4 x hx
    have hsp := sigmaF_pos (show 1 ≤ x by omega)
    constructor
    · intro hev
      have hp : (-1 : ℝ) ^ x = 1 := Even.neg_one_pow (Nat.even_iff.2 hev)
      by_cases hxM : x ≤ M
      · rw [hxlow x hx hxM, hp]
        constructor <;> linarith
      · rw [hxhigh x (by omega) hx, hp]
        obtain ⟨g0, g1⟩ := hG x (by omega)
        have := hGA x (by omega)
        constructor <;> linarith
    · intro hod
      have hp : (-1 : ℝ) ^ x = -1 := Odd.neg_one_pow (Nat.odd_iff.2 hod)
      by_cases hxM : x ≤ M
      · rw [hxlow x hx hxM, hp]
        have hs5x := hs5 x (by omega)
        constructor <;> linarith
      · rw [hxhigh x (by omega) hx, hp]
        obtain ⟨g0, g1⟩ := hG x (by omega)
        have : 0 < 1 / ((M : ℝ) + 1) := by positivity
        constructor <;> linarith
  have hpair : ∀ x y, 4 ≤ y → y < x → (x - y) % 2 = 1 →
      0 ≤ dipTau 1 M (2 / 7) x + dipTau 1 M (2 / 7) y ∧
        dipTau 1 M (2 / 7) x + dipTau 1 M (2 / 7) y ≤ 2 := by
    intro x y hy hyx hodd
    have sxy : (-1 : ℝ) ^ x = -(-1) ^ y := by
      have := neg_one_pow_of_odd_sub hyx hodd 0
      simpa using this
    have hsx := hs4 x (by omega)
    have hsy := hs4 y hy
    have hspx := sigmaF_pos (show 1 ≤ x by omega)
    have hspy := sigmaF_pos (show 1 ≤ y by omega)
    by_cases hxM : x ≤ M
    · rw [hxlow x (by omega) hxM, hxlow y hy (by omega), sxy]
      constructor <;> linarith
    · by_cases hyM : y ≤ M
      · rw [hxhigh x (by omega) (by omega), hxlow y hy hyM, sxy]
        obtain ⟨g0, g1⟩ := hG x (by omega)
        have hs := sigmaF_anti (show 1 ≤ M + 1 by omega) (show M + 1 ≤ x by omega)
        have hGx := mul_le_mul_of_nonneg_left hs hM1
        have hsM := sigmaF_pos (show 1 ≤ M + 1 by omega)
        obtain ⟨s1, s2⟩ := neg_one_pow_bound haM0.le (y + M)
        have e : (-1 : ℝ) ^ (y + M) * aF M = (-1) ^ y * ((-1) ^ M * aF M) := by
          rw [pow_add]
          ring
        rw [e] at s1 s2
        have hexp : -(-1 : ℝ) ^ y * (aF 1 - 2 / 21 + (-1) ^ M * aF M) + (-1) ^ y * (aF 1 - 2 / 21) =
            -((-1) ^ y * ((-1) ^ M * aF M)) := by ring
        constructor <;> linarith
      · rw [hxhigh x (by omega) (by omega), hxhigh y (by omega) hy, sxy]
        obtain ⟨g0, g1⟩ := hG x (by omega)
        obtain ⟨g2, g3⟩ := hG y (by omega)
        have : 0 < 1 / ((M : ℝ) + 1) := by positivity
        constructor <;> linarith
  refine ⟨fun x y hy hyx hxn hodd => ?_, fun x hx hxn hodd => ?_⟩
  · by_cases hy4 : 4 ≤ y
    · rw [if_neg (show ¬ (y = 1 + 1) by omega), sub_zero]
      exact hpair x y hy4 hyx hodd
    · interval_cases y
      · rw [if_neg (by omega), sub_zero, t1, add_zero]
        by_cases hx2 : x = 2
        · subst hx2
          rw [t2]
          norm_num
        · obtain ⟨h1, h2⟩ := (hbig x (by omega)).1 (by omega)
          constructor <;> linarith
      · rw [if_pos rfl, t2]
        by_cases hx3 : x = 3
        · subst hx3
          rw [t3]
          split_ifs <;> norm_num
        · obtain ⟨h1, h2⟩ := (hbig x (by omega)).2 (by omega)
          constructor <;> linarith
      · rw [if_neg (by omega), sub_zero, t3]
        obtain ⟨h1, h2⟩ := (hbig x (by omega)).1 (by omega)
        split_ifs with hM2
        · constructor <;> linarith
        · constructor <;> linarith
  · by_cases hx5 : 5 ≤ x
    · rw [if_pos (by omega)]
      have hp : (-1 : ℝ) ^ x = -1 := Odd.neg_one_pow (Nat.odd_iff.2 hodd)
      by_cases hxM : x ≤ M
      · rw [hxlow x (by omega) hxM, hp]
        have := hs5 x hx5
        have := sigmaF_pos (show 1 ≤ x by omega)
        constructor <;> linarith
      · rw [hxhigh x (by omega) (by omega), hp]
        obtain ⟨g0, g1⟩ := hG x (by omega)
        have : 0 < 1 / ((M : ℝ) + 1) := by positivity
        constructor <;> linarith
    · rw [if_neg (by omega), add_zero]
      rcases (show x = 1 ∨ x = 3 by omega) with rfl | rfl
      · rw [t1]
        norm_num
      · rw [t3]
        split_ifs <;> norm_num

end CaseD

/-! ## All intervals of all boxes -/

/-- **Interval uniformisations exist for every interval of every box** (P-PROOF). -/
theorem intervalUnifAll_all (n : ℕ) : IntervalUnifAll n := by
  intro lo hi hlohi hhi
  by_cases hlo : lo = 0
  · subst hlo
    by_cases hh : hi + 1 = n
    · obtain rfl : hi = n - 1 := by omega
      exact ⟨boxJ n, isIntervalUnif_boxJ (by omega)⟩
    · exact ⟨renU n hi, isIntervalUnif_renU (by omega)⟩
  by_cases hh : hi + 1 = n
  · obtain ⟨m, rfl⟩ : ∃ m, lo = m + 1 := ⟨lo - 1, by omega⟩
    obtain rfl : hi = n - 1 := by omega
    exact ⟨_, (isIntervalUnif_renU (show m + 2 ≤ n by omega)).compl (by omega)⟩
  have hhi2 : hi + 2 ≤ n := by omega
  have hlo1 : 1 ≤ lo := by omega
  by_cases hC : n ≤ 2 * (n - 1 - hi) + 1
  · refine ⟨dipU n lo hi 0, isIntervalUnif_dip hlo1 hlohi hhi2 (Or.inl rfl) ?_ ?_⟩
    · by_cases hK1 : n - 1 - hi = 1
      · have hn3 : n = 3 := by omega
        have hl : lo = 1 := by omega
        have hh1 : hi = 1 := by omega
        subst hn3 hl hh1
        exact caseC_K1_cells.1
      · exact (caseC_cells (show 2 ≤ n - 1 - hi by omega) (show n - 1 - hi + 1 ≤ n - lo by omega)
          hC).1
    · by_cases hK1 : n - 1 - hi = 1
      · have hn3 : n = 3 := by omega
        have hl : lo = 1 := by omega
        have hh1 : hi = 1 := by omega
        subst hn3 hl hh1
        exact caseC_K1_cells.2
      · exact (caseC_cells (show 2 ≤ n - 1 - hi by omega) (show n - 1 - hi + 1 ≤ n - lo by omega)
          hC).2
  by_cases hD : n - 1 - hi = 1
  · refine ⟨dipU n lo hi (2 / 7), isIntervalUnif_dip hlo1 hlohi hhi2 (Or.inr (by omega)) ?_ ?_⟩
    · rw [hD]
      exact (caseD_cells (M := n - lo) (show 2 ≤ n - lo by omega) (show n - lo + 1 ≤ n by omega)).1
    · rw [hD]
      exact (caseD_cells (M := n - lo) (show 2 ≤ n - lo by omega) (show n - lo + 1 ≤ n by omega)).2
  · refine ⟨dipU n lo hi (alphaStar (n - 1 - hi) (n - lo)),
      isIntervalUnif_dip hlo1 hlohi hhi2 (Or.inr (by omega)) ?_ ?_⟩
    · exact (caseE_cells (show 2 ≤ n - 1 - hi by omega) (show n - 1 - hi + 1 ≤ n - lo by omega)).1
    · exact (caseE_cells (show 2 ≤ n - 1 - hi by omega) (show n - 1 - hi + 1 ≤ n - lo by omega)).2

end STUProof
