import STUProof.Construction

/-!
# Step 2: the thermal point lies in `conv {v_0(p), …, v_{d-1}(p)}` (Lemma 5 of arXiv:1904.07942)

Let `E_0 ≤ … ≤ E_{d-1}`, `β > 0`, `0 ≤ β' ≤ β`, `p = Gibbs(β)` and `q = Gibbs(β')`. Then
`q = ∑_k c_k v_k(p)` with explicit barycentric coordinates `c_k ≥ 0`, `∑ c_k = 1` (`lemma5`).

## Proof

For a vector `u` put `F_m(u) = u_0 + … + u_m - (m + 1) u_{m+1}` (`fF`). Then
`F_m(v_k(p)) = F_m(p)` if `k ≤ m` and `0` otherwise (`fF_vN`), and a vector with sum `0` and
all `F_m = 0` vanishes (`eq_zero_of_fF`). Hence `q = ∑ c_k v_k` with
`∑_{k ≤ m} c_k = ρ_m := F_m(q) / F_m(p)` for `m ≤ d - 2`. The weights are nonnegative iff
`0 ≤ ρ_0 ≤ ρ_1 ≤ … ≤ ρ_{d-2} ≤ 1`.

* `ρ_m ≤ ρ_{m+1}` reduces to `F_m(q) (p_{m+1} - p_{m+2}) ≤ (q_{m+1} - q_{m+2}) F_m(p)`. Term by
  term this is the three-point inequality `three_point` for `E_i ≤ E_{m+1} ≤ E_{m+2}`. It follows
  from `β (e^{β' y} - 1) ≤ β' (e^{β y} - 1)` (convexity of `exp`, `exp_chord`), used once with
  `y = E_{m+1} - E_i ≥ 0` and once with `y = E_{m+1} - E_{m+2} ≤ 0`.
* `ρ_{d-2} ≤ 1` is `p_{d-1} ≤ q_{d-1}`: the top level gains weight when `β` decreases.
-/

open Finset

noncomputable section

namespace STUProof

/-! ## Gibbs weights -/

/-- Gibbs weights `p_i = e^{-β E_i} / ∑_j e^{-β E_j}`. -/
def gibbs {d : ℕ} (E : Fin d → ℝ) (β : ℝ) : Fin d → ℝ :=
  fun i => Real.exp (-β * E i) / ∑ j, Real.exp (-β * E j)

theorem gibbs_Z_pos {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (β : ℝ) :
    0 < ∑ j, Real.exp (-β * E j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hd⟩, Finset.mem_univ _⟩

theorem gibbs_nonneg {d : ℕ} (E : Fin d → ℝ) (β : ℝ) (i : Fin d) : 0 ≤ gibbs E β i :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))

theorem gibbs_sum {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (β : ℝ) : ∑ i, gibbs E β i = 1 := by
  unfold gibbs
  rw [← Finset.sum_div, div_self (gibbs_Z_pos hd E β).ne']

theorem gibbs_antitone {d : ℕ} (E : Fin d → ℝ) (hE : Monotone E) {β : ℝ} (hβ : 0 ≤ β) :
    Antitone (gibbs E β) := by
  intro i j hij
  unfold gibbs
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le))
  apply Real.exp_le_exp.2
  nlinarith [hE hij]

/-! ## Exponential inequalities -/

/-- `β (e^{β' y} - 1) ≤ β' (e^{β y} - 1)` for `0 ≤ β' ≤ β`, `0 < β` (convexity of `exp`). -/
theorem exp_chord (y : ℝ) {β β' : ℝ} (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    β * (Real.exp (β' * y) - 1) ≤ β' * (Real.exp (β * y) - 1) := by
  have ht0 : 0 ≤ β' / β := div_nonneg h0 hβ.le
  have ht1 : 0 ≤ 1 - β' / β := sub_nonneg.2 ((div_le_one hβ).2 h1)
  have hconv := convexOn_exp.2 (Set.mem_univ (β * y)) (Set.mem_univ 0) ht0 ht1
    (by ring : β' / β + (1 - β' / β) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have e : β' / β * (β * y) = β' * y := by field_simp
  rw [e] at hconv
  have h := mul_le_mul_of_nonneg_left hconv hβ.le
  have e2 : β * (β' / β * Real.exp (β * y) + (1 - β' / β)) =
      β' * Real.exp (β * y) + (β - β') := by
    field_simp
  rw [e2] at h
  linarith

/-- The three-point inequality: for `a ≤ b ≤ c` and `0 ≤ β' ≤ β`,
`(e^{-β'a} - e^{-β'b})(e^{-βb} - e^{-βc}) ≤ (e^{-β'b} - e^{-β'c})(e^{-βa} - e^{-βb})`. -/
theorem three_point {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {β β' : ℝ} (hβ : 0 < β)
    (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    (Real.exp (-β' * a) - Real.exp (-β' * b)) * (Real.exp (-β * b) - Real.exp (-β * c)) ≤
      (Real.exp (-β' * b) - Real.exp (-β' * c)) * (Real.exp (-β * a) - Real.exp (-β * b)) := by
  set X := Real.exp (β' * (b - a)) - 1 with hX
  set Xs := Real.exp (β * (b - a)) - 1 with hXs
  set Y := 1 - Real.exp (-(β * (c - b))) with hY
  set Y' := 1 - Real.exp (-(β' * (c - b))) with hY'
  have e1 : Real.exp (-β' * a) - Real.exp (-β' * b) = Real.exp (-β' * b) * X := by
    rw [hX, show -β' * a = -β' * b + β' * (b - a) by ring, Real.exp_add]
    ring
  have e2 : Real.exp (-β * b) - Real.exp (-β * c) = Real.exp (-β * b) * Y := by
    rw [hY, show -β * c = -β * b + -(β * (c - b)) by ring, Real.exp_add]
    ring
  have e3 : Real.exp (-β' * b) - Real.exp (-β' * c) = Real.exp (-β' * b) * Y' := by
    rw [hY', show -β' * c = -β' * b + -(β' * (c - b)) by ring, Real.exp_add]
    ring
  have e4 : Real.exp (-β * a) - Real.exp (-β * b) = Real.exp (-β * b) * Xs := by
    rw [hXs, show -β * a = -β * b + β * (b - a) by ring, Real.exp_add]
    ring
  rw [e1, e2, e3, e4]
  have hX0 : 0 ≤ X := by
    rw [hX, sub_nonneg]
    exact Real.one_le_exp (mul_nonneg h0 (sub_nonneg.2 hab))
  have hXs0 : 0 ≤ Xs := by
    rw [hXs, sub_nonneg]
    exact Real.one_le_exp (mul_nonneg hβ.le (sub_nonneg.2 hab))
  have hY0 : 0 ≤ Y := by
    rw [hY, sub_nonneg]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hβ.le (sub_nonneg.2 hbc)))
  have hY'0 : 0 ≤ Y' := by
    rw [hY', sub_nonneg]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg h0 (sub_nonneg.2 hbc)))
  have key : X * Y ≤ Y' * Xs := by
    rcases eq_or_lt_of_le h0 with h | h
    · have : X = 0 := by rw [hX, ← h, zero_mul, Real.exp_zero, sub_self]
      rw [this, zero_mul]
      exact mul_nonneg hY'0 hXs0
    · have hA : β * X ≤ β' * Xs := exp_chord (b - a) hβ h0 h1
      have hB' := exp_chord (-(c - b)) hβ h0 h1
      rw [mul_neg, mul_neg] at hB'
      have hB : β' * Y ≤ β * Y' := by
        rw [hY, hY']
        linarith
      have hprod : β * X * (β' * Y) ≤ β' * Xs * (β * Y') :=
        mul_le_mul hA hB (mul_nonneg h0 hY0) (mul_nonneg h0 hXs0)
      have hprod' : (β * β') * (X * Y) ≤ (β * β') * (Y' * Xs) := by
        linarith [hprod]
      exact le_of_mul_le_mul_left hprod' (mul_pos hβ h)
  have hpos : 0 ≤ Real.exp (-β' * b) * Real.exp (-β * b) := by positivity
  calc Real.exp (-β' * b) * X * (Real.exp (-β * b) * Y)
      = (Real.exp (-β' * b) * Real.exp (-β * b)) * (X * Y) := by ring
    _ ≤ (Real.exp (-β' * b) * Real.exp (-β * b)) * (Y' * Xs) :=
        mul_le_mul_of_nonneg_left key hpos
    _ = Real.exp (-β' * b) * Y' * (Real.exp (-β * b) * Xs) := by ring

/-! ## The abstract barycentric lemma (vectors indexed by `ℕ`) -/

/-- Partial sums `u_0 + … + u_m`. -/
def psum (u : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ range (m + 1), u i

/-- `F_m(u) = u_0 + … + u_m - (m + 1) u_{m+1}`. -/
def fF (u : ℕ → ℝ) (m : ℕ) : ℝ := psum u m - (m + 1) * u (m + 1)

/-- `v_k(u)` for vectors indexed by `ℕ`. -/
def vN (u : ℕ → ℝ) (k i : ℕ) : ℝ := if i ≤ k then psum u k / (k + 1) else u i

theorem fF_eq_sum (u : ℕ → ℝ) (m : ℕ) : fF u m = ∑ i ∈ range (m + 1), (u i - u (m + 1)) := by
  rw [fF, psum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem fF_succ (u : ℕ → ℝ) (m : ℕ) :
    fF u (m + 1) = fF u m + (m + 2) * (u (m + 1) - u (m + 2)) := by
  simp only [fF, psum, Finset.sum_range_succ]
  push_cast
  ring

theorem psum_vN_of_le (u : ℕ → ℝ) {k m : ℕ} (hkm : k ≤ m) : psum (vN u k) m = psum u m := by
  unfold psum
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ m + 1),
    ← Finset.sum_range_add_sum_Ico (fun i => u i) (by omega : k + 1 ≤ m + 1)]
  congr 1
  · have : ∀ i ∈ range (k + 1), vN u k i = psum u k / (k + 1) := by
      intro i hi
      have : i ≤ k := by rw [Finset.mem_range] at hi; omega
      simp [vN, this]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, psum]
    push_cast
    field_simp
  · apply Finset.sum_congr rfl
    intro i hi
    have : ¬ i ≤ k := by rw [Finset.mem_Ico] at hi; omega
    simp [vN, this]

theorem fF_vN (u : ℕ → ℝ) (k m : ℕ) : fF (vN u k) m = if k ≤ m then fF u m else 0 := by
  split_ifs with h
  · rw [fF, fF, psum_vN_of_le u h]
    have : ¬ m + 1 ≤ k := by omega
    simp [vN, this]
  · have hall : ∀ i ∈ range (m + 1), vN u k i = psum u k / (k + 1) := by
      intro i hi
      have : i ≤ k := by rw [Finset.mem_range] at hi; omega
      simp [vN, this]
    have htop : vN u k (m + 1) = psum u k / (k + 1) := by
      have : m + 1 ≤ k := by omega
      simp [vN, this]
    rw [fF, psum, Finset.sum_congr rfl hall, htop, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    ring

theorem sum_vN (u : ℕ → ℝ) {k d : ℕ} (hk : k < d) :
    ∑ i ∈ range d, vN u k i = ∑ i ∈ range d, u i := by
  have h := psum_vN_of_le u (le_refl k)
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ d),
    ← Finset.sum_range_add_sum_Ico u (by omega : k + 1 ≤ d)]
  unfold psum at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have : ¬ i ≤ k := by rw [Finset.mem_Ico] at hi; omega
  simp [vN, this]

/-- A vector with zero sum and `F_m = 0` for all `m + 1 < d` vanishes on `{0, …, d-1}`. -/
theorem eq_zero_of_fF {d : ℕ} (hd : 0 < d) (u : ℕ → ℝ) (h1 : ∑ i ∈ range d, u i = 0)
    (h2 : ∀ m, m + 1 < d → fF u m = 0) : ∀ i < d, u i = 0 := by
  have hconst : ∀ i, i < d → u i = u 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      cases i with
      | zero => rfl
      | succ m =>
        have hm := h2 m hi
        have hs : ∑ j ∈ range (m + 1), u j = (m + 1) * u 0 := by
          rw [Finset.sum_congr rfl (fun j hj => ih j (by rw [Finset.mem_range] at hj; omega)
            (by rw [Finset.mem_range] at hj; omega))]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
        rw [fF, psum, hs] at hm
        have hm' : ((m : ℝ) + 1) * (u (m + 1) - u 0) = 0 := by linarith
        rcases mul_eq_zero.1 hm' with h | h
        · have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
          linarith
        · linarith
  have h0 : u 0 = 0 := by
    have : ∑ i ∈ range d, u i = d * u 0 := by
      rw [Finset.sum_congr rfl (fun i hi => hconst i (Finset.mem_range.1 hi)),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [this] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · have : (0 : ℝ) < d := by exact_mod_cast hd
      linarith
    · exact h
  intro i hi
  rw [hconst i hi, h0]

/-- **Abstract form of Lemma 5.** Under the displayed hypotheses on the sorted probability
vectors `P` and `Q`, `Q` is a convex combination of `v_0(P), …, v_{d-1}(P)`. -/
theorem conv_vN {d : ℕ} (hd : 0 < d) (P Q : ℕ → ℝ)
    (hPanti : ∀ i j, i ≤ j → j < d → P j ≤ P i)
    (hQanti : ∀ i j, i ≤ j → j < d → Q j ≤ Q i)
    (hPs : ∑ i ∈ range d, P i = 1) (hQs : ∑ i ∈ range d, Q i = 1)
    (hzero : ∀ m, m + 1 < d → fF P m = 0 → fF Q m = 0)
    (hcore : ∀ m, m + 2 < d →
      fF Q m * (P (m + 1) - P (m + 2)) ≤ (Q (m + 1) - Q (m + 2)) * fF P m)
    (hlast : P (d - 1) ≤ Q (d - 1)) :
    ∃ c : ℕ → ℝ, (∀ k < d, 0 ≤ c k) ∧ ∑ k ∈ range d, c k = 1 ∧
      ∀ i < d, ∑ k ∈ range d, c k * vN P k i = Q i := by
  -- cumulative weights
  set cum : ℕ → ℝ := fun j => if j = 0 then 0 else if j < d then fF Q (j - 1) / fF P (j - 1)
    else 1 with hcum
  have hFP : ∀ m, m + 1 < d → 0 ≤ fF P m := by
    intro m hm
    rw [fF_eq_sum]
    exact Finset.sum_nonneg (fun i hi => sub_nonneg.2
      (hPanti i (m + 1) (by rw [Finset.mem_range] at hi; omega) hm))
  have hFQ : ∀ m, m + 1 < d → 0 ≤ fF Q m := by
    intro m hm
    rw [fF_eq_sum]
    exact Finset.sum_nonneg (fun i hi => sub_nonneg.2
      (hQanti i (m + 1) (by rw [Finset.mem_range] at hi; omega) hm))
  have hmono : ∀ m, m + 2 < d → fF Q m / fF P m ≤ fF Q (m + 1) / fF P (m + 1) := by
    intro m hm
    have hr0 : 0 ≤ fF Q (m + 1) / fF P (m + 1) :=
      div_nonneg (hFQ (m + 1) (by omega)) (hFP (m + 1) (by omega))
    rcases eq_or_lt_of_le (hFP m (by omega)) with h | h
    · rw [← h, div_zero]
      exact hr0
    · have hDP : 0 ≤ P (m + 1) - P (m + 2) := sub_nonneg.2 (hPanti _ _ (by omega) hm)
      have hsP := fF_succ P m
      have hsQ := fF_succ Q m
      have hP1 : 0 < fF P (m + 1) := by
        rw [hsP]
        have : (0 : ℝ) ≤ ((m : ℝ) + 2) * (P (m + 1) - P (m + 2)) := by positivity
        linarith
      rw [div_le_div_iff₀ h hP1, hsP, hsQ]
      have hc := hcore m hm
      have hm2 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hc hm2]
  have hlast' : 2 ≤ d → fF Q (d - 2) / fF P (d - 2) ≤ 1 := by
    intro h2
    have hF : ∀ u : ℕ → ℝ, ∑ i ∈ range d, u i = 1 → fF u (d - 2) = 1 - d * u (d - 1) := by
      intro u hu
      have e1 : d - 2 + 1 = d - 1 := by omega
      rw [fF, psum, e1]
      have e2 : ∑ i ∈ range (d - 1), u i = 1 - u (d - 1) := by
        have := Finset.sum_range_succ u (d - 1)
        rw [show d - 1 + 1 = d by omega, hu] at this
        linarith
      rw [e2]
      have e3 : ((d - 2 : ℕ) : ℝ) + 1 = d - 1 := by
        rw [show d - 2 = (d - 1) - 1 by omega]
        have : 1 ≤ d - 1 := by omega
        push_cast [this, show 1 ≤ d by omega]
        ring
      rw [e3]
      ring
    rcases eq_or_lt_of_le (hFP (d - 2) (by omega)) with h | h
    · rw [← h, div_zero]
      exact zero_le_one
    · rw [div_le_one h, hF P hPs, hF Q hQs]
      have : (0 : ℝ) ≤ d := by positivity
      nlinarith
  have hcum0 : cum 0 = 0 := by simp [hcum]
  have hcumd : cum d = 1 := by simp [hcum, hd.ne']
  have hcumj : ∀ j, 0 < j → j < d → cum j = fF Q (j - 1) / fF P (j - 1) := by
    intro j h1 h2
    simp [hcum, h1.ne', h2]
  refine ⟨fun k => cum (k + 1) - cum k, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro k hk
    show 0 ≤ cum (k + 1) - cum k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [hcum0, sub_zero]
      rcases Nat.lt_or_ge 1 d with h1 | h1
      · rw [hcumj 1 one_pos h1]
        exact div_nonneg (hFQ 0 (by omega)) (hFP 0 (by omega))
      · rw [show (0 + 1 : ℕ) = d by omega, hcumd]
        exact zero_le_one
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hcumj (k' + 1) (by omega) hk, Nat.add_sub_cancel]
      rcases Nat.lt_or_ge (k' + 1 + 1) d with h1 | h1
      · rw [hcumj (k' + 1 + 1) (by omega) h1, Nat.add_sub_cancel]
        have := hmono k' (by omega)
        linarith
      · rw [show k' + 1 + 1 = d by omega, hcumd]
        have hd' : k' = d - 2 := by omega
        have := hlast' (by omega)
        rw [← hd'] at this
        linarith
  · -- the weights sum to one
    rw [Finset.sum_range_sub (fun j => cum j) d, hcumd, hcum0, sub_zero]
  · -- reconstruction
    set c : ℕ → ℝ := fun k => cum (k + 1) - cum k with hc
    set G : ℕ → ℝ := fun i => ∑ k ∈ range d, c k * vN P k i with hG
    have hcs : ∑ k ∈ range d, c k = 1 := by
      rw [Finset.sum_range_sub (fun j => cum j) d, hcumd, hcum0, sub_zero]
    have hGsum : ∑ i ∈ range d, G i = 1 := by
      simp only [hG]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun k hk => by
        rw [← Finset.mul_sum, sum_vN P (Finset.mem_range.1 hk), hPs, mul_one])]
      exact hcs
    have hcsum : ∀ m, ∑ k ∈ range (m + 1), c k = cum (m + 1) := by
      intro m
      rw [Finset.sum_range_sub (fun j => cum j) (m + 1), hcum0, sub_zero]
    have hGF : ∀ m, m + 1 < d → fF G m = fF Q m := by
      intro m hm
      have e1 : fF G m = ∑ k ∈ range d, c k * fF (vN P k) m := by
        simp only [hG, fF, psum]
        rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_sub, Finset.mul_sum]
        ring
      rw [e1]
      simp_rw [fF_vN]
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ d)]
      have e2 : ∑ k ∈ Ico (m + 1) d, c k * (if k ≤ m then fF P m else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have : ¬ k ≤ m := by rw [Finset.mem_Ico] at hk; omega
        simp [this]
      have e3 : ∑ k ∈ range (m + 1), c k * (if k ≤ m then fF P m else 0) =
          (∑ k ∈ range (m + 1), c k) * fF P m := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have : k ≤ m := by rw [Finset.mem_range] at hk; omega
        simp [this]
      rw [e2, e3, add_zero, hcsum m, hcumj (m + 1) (by omega) hm, Nat.add_sub_cancel]
      rcases eq_or_ne (fF P m) 0 with h | h
      · rw [h, mul_zero, hzero m hm h]
      · field_simp
    have hzero' := eq_zero_of_fF hd (fun i => G i - Q i)
      (by rw [Finset.sum_sub_distrib, hGsum, hQs, sub_self])
      (by
        intro m hm
        have : fF (fun i => G i - Q i) m = fF G m - fF Q m := by
          simp only [fF, psum, Finset.sum_sub_distrib]
          ring
        rw [this, hGF m hm, sub_self])
    intro i hi
    have := hzero' i hi
    simp only [hG] at this
    linarith

/-! ## Lemma 5 for Gibbs states -/

/-- Extension by zero of a vector on `Fin d` to `ℕ`. -/
def extN {d : ℕ} (u : Fin d → ℝ) : ℕ → ℝ := fun i => if h : i < d then u ⟨i, h⟩ else 0

theorem extN_lt {d : ℕ} (u : Fin d → ℝ) {i : ℕ} (h : i < d) : extN u i = u ⟨i, h⟩ := dif_pos h

theorem sum_extN {d : ℕ} (u : Fin d → ℝ) : ∑ i ∈ range d, extN u i = ∑ i, u i := by
  rw [← Fin.sum_univ_eq_sum_range (extN u) d]
  exact Finset.sum_congr rfl (fun i _ => extN_lt u i.isLt)

theorem psum_extN {d : ℕ} (u : Fin d → ℝ) (k : Fin d) :
    psum (extN u) k = ∑ j with j ≤ k, u j := by
  rw [Finset.sum_filter]
  have h : ∑ j : Fin d, (if j ≤ k then u j else 0) =
      ∑ j ∈ range d, (if j ≤ (k : ℕ) then extN u j else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if j ≤ (k : ℕ) then extN u j else 0) d]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.le_iff_val_le_val, extN_lt u j.isLt]
  rw [h, psum, ← Finset.sum_range_add_sum_Ico _ (by omega : (k : ℕ) + 1 ≤ d)]
  have h1 : ∑ j ∈ Ico ((k : ℕ) + 1) d, (if j ≤ (k : ℕ) then extN u j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have : ¬ j ≤ (k : ℕ) := by rw [Finset.mem_Ico] at hj; omega
    simp [this]
  rw [h1, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have : j ≤ (k : ℕ) := by rw [Finset.mem_range] at hj; omega
  simp [this]

theorem vk_eq_vN {d : ℕ} (u : Fin d → ℝ) (k i : Fin d) : vk u k i = vN (extN u) k i := by
  unfold vk vN
  rw [psum_extN, extN_lt u i.isLt]
  by_cases h : i ≤ k
  · rw [if_pos h, if_pos (Fin.le_iff_val_le_val.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (Fin.le_iff_val_le_val.2 h'))]

/-- The top level gains weight when the temperature increases. -/
theorem gibbs_top_le {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ}
    (h1 : β' ≤ β) :
    gibbs E β ⟨d - 1, by omega⟩ ≤ gibbs E β' ⟨d - 1, by omega⟩ := by
  unfold gibbs
  rw [div_le_div_iff₀ (gibbs_Z_pos hd E β) (gibbs_Z_pos hd E β'), Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hj : E j ≤ E ⟨d - 1, by omega⟩ := hE (Fin.mk_le_mk.2 (by omega) : j ≤ ⟨d - 1, by omega⟩)
  nlinarith

/-- **Lemma 5 of arXiv:1904.07942.** For `E_0 ≤ … ≤ E_{d-1}`, `β > 0` and `0 ≤ β' ≤ β`, the Gibbs
vector at `β'` is an explicit convex combination of `v_0(p), …, v_{d-1}(p)`, `p = Gibbs(β)`. -/
theorem lemma5 {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ}
    (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ c : Fin d → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k = 1 ∧
      ∑ k, c k • vk (gibbs E β) k = gibbs E β' := by
  set p := gibbs E β with hp
  set q := gibbs E β' with hq
  have hZ := gibbs_Z_pos hd E β
  have hZ' := gibbs_Z_pos hd E β'
  have hpA : Antitone p := gibbs_antitone E hE hβ.le
  have hqA : Antitone q := gibbs_antitone E hE h0
  have hPanti : ∀ i j, i ≤ j → j < d → extN p j ≤ extN p i := by
    intro i j hij hj
    rw [extN_lt p hj, extN_lt p (lt_of_le_of_lt hij hj)]
    exact hpA (Fin.mk_le_mk.2 hij)
  have hQanti : ∀ i j, i ≤ j → j < d → extN q j ≤ extN q i := by
    intro i j hij hj
    rw [extN_lt q hj, extN_lt q (lt_of_le_of_lt hij hj)]
    exact hqA (Fin.mk_le_mk.2 hij)
  have hPs : ∑ i ∈ range d, extN p i = 1 := by rw [sum_extN]; exact gibbs_sum hd E β
  have hQs : ∑ i ∈ range d, extN q i = 1 := by rw [sum_extN]; exact gibbs_sum hd E β'
  have hzero : ∀ m, m + 1 < d → fF (extN p) m = 0 → fF (extN q) m = 0 := by
    intro m hm h
    rw [fF_eq_sum] at h ⊢
    have hnn : ∀ i ∈ range (m + 1), 0 ≤ extN p i - extN p (m + 1) := fun i hi =>
      sub_nonneg.2 (hPanti i (m + 1) (by rw [Finset.mem_range] at hi; omega) hm)
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < d := by rw [Finset.mem_range] at hi; omega
    have h' := h i hi
    rw [extN_lt p hi', extN_lt p hm, sub_eq_zero, hp] at h'
    unfold gibbs at h'
    rw [div_left_inj' hZ.ne', Real.exp_eq_exp] at h'
    have hEeq : E ⟨i, hi'⟩ = E ⟨m + 1, hm⟩ := mul_left_cancel₀ (neg_ne_zero.2 hβ.ne') h'
    rw [extN_lt q hi', extN_lt q hm, sub_eq_zero, hq]
    unfold gibbs
    rw [hEeq]
  have hcore : ∀ m, m + 2 < d → fF (extN q) m * (extN p (m + 1) - extN p (m + 2)) ≤
      (extN q (m + 1) - extN q (m + 2)) * fF (extN p) m := by
    intro m hm
    rw [fF_eq_sum, fF_eq_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < d := by rw [Finset.mem_range] at hi; omega
    rw [extN_lt p hi', extN_lt p (by omega : m + 1 < d), extN_lt p hm, extN_lt q hi',
      extN_lt q (by omega : m + 1 < d), extN_lt q hm, hp, hq]
    unfold gibbs
    rw [div_sub_div_same, div_sub_div_same, div_sub_div_same, div_sub_div_same,
      div_mul_div_comm, div_mul_div_comm]
    apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos hZ' hZ))
    exact three_point (hE (Fin.mk_le_mk.2 (by rw [Finset.mem_range] at hi; omega)))
      (hE (Fin.mk_le_mk.2 (by omega))) hβ h0 h1
  have hlast : extN p (d - 1) ≤ extN q (d - 1) := by
    rw [extN_lt p (by omega), extN_lt q (by omega), hp, hq]
    exact gibbs_top_le hd E hE h1
  obtain ⟨c, hc0, hc1, hcv⟩ :=
    conv_vN hd (extN p) (extN q) hPanti hQanti hPs hQs hzero hcore hlast
  refine ⟨fun k => c k, fun k => hc0 k k.isLt, ?_, ?_⟩
  · rw [Fin.sum_univ_eq_sum_range c d]
    exact hc1
  · funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, vk_eq_vN]
    rw [Fin.sum_univ_eq_sum_range (fun k => c k * vN (extN p) k i) d, hcv i i.isLt,
      extN_lt q i.isLt]

/-- Lemma 5 as a convex-hull statement. -/
theorem gibbs_mem_convexHull {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (hE : Monotone E)
    {β β' : ℝ} (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    gibbs E β' ∈ convexHull ℝ (Set.range (vk (gibbs E β))) := by
  obtain ⟨c, hc0, hc1, hcv⟩ := lemma5 hd E hE hβ h0 h1
  rw [← hcv]
  exact (convex_convexHull ℝ _).sum_mem (fun k _ => hc0 k) hc1
    (fun k _ => subset_convexHull ℝ _ (Set.mem_range_self k))

end STUProof
