import STUProof.IntervalUnif

/-!
# The renewal square

For `0 ≤ m ≤ n - 2` let `K = n - m - 1` and `H(ℓ) = 1 - K²/((n-ℓ)(n-ℓ+1))` for `1 ≤ ℓ ≤ m+1`,
`H(ℓ) = 0` for `ℓ > m+1` (P-UNIF, `iqoqi/programs/unif/LOG.md`). The *renewal square* `U^m_n` is the
superposition of the reversal permutations of the blocks `[0, ℓ-1]`, `[n-ℓ, n-1]` (weight `H(ℓ)`)
and `[a, a+ℓ-1]`, `1 ≤ a ≤ n-1-ℓ` (weight `H(ℓ) - H(ℓ+1)`). Its cells have the Toeplitz + Hankel
form (`renU`)
  `U(i, j) = A(|i-j| + 1) + A(min(i+j+2, 2n-i-j))`,  `A(p) = ∑_t (-1)^t H(p+t)`,
equivalently `U(i, j) = ∑_{t=0}^{2k} (-1)^t H(|i-j|+1+t)`, `k = min(i, j, n-1-i, n-1-j)` (checked
against the block construction for all `n ≤ 30`). We prove, for all `n`:
* `0 ≤ U ≤ 1` (an alternating sum of a nonincreasing nonnegative sequence), `U = 0` off the band
  `|i-j| ≤ m`;
* rows: every row sum is `∑_ℓ H(ℓ) = (m+1)²/n` (`renU_row_succ`: shifting the row by one changes
  the Toeplitz and the Hankel part by opposite amounts);
* runs: `R(s) = W(s+1) + R(s+2)` with the length totals `W(ℓ) = 2H(ℓ) + (n-ℓ-1)(H(ℓ)-H(ℓ+1))`,
  `W(ℓ) = 2` for `ℓ ≤ m` and `W(m+1) = 1`, hence `R(s) = m+1-s` for `s ≤ m`.

Hence `U^m_n` is an interval uniformisation of `[0, m]` (`isIntervalUnif_renU`), the all-ones
square `J` one of `[0, n-1]` (`isIntervalUnif_boxJ`), and `J - U^{lo-1}_n` one of `[lo, n-1]`
(`IsIntervalUnif.compl`).
-/

open Finset

noncomputable section

namespace STUProof

/-! ## Definitions -/

/-- `K = n - m - 1`. -/
def renK (n m : ℕ) : ℝ := (n : ℝ) - m - 1

/-- Block weights `H(ℓ) = 1 - K²/((n-ℓ)(n-ℓ+1))` for `1 ≤ ℓ ≤ m+1`, and `0` otherwise. -/
def renH (n m ℓ : ℕ) : ℝ :=
  if 1 ≤ ℓ ∧ ℓ ≤ m + 1 then 1 - renK n m ^ 2 / (((n : ℝ) - ℓ) * ((n : ℝ) - ℓ + 1)) else 0

/-- Alternating tails `A(p) = ∑_{t ≤ m+1} (-1)^t H(p + t)`. -/
def renA (n m p : ℕ) : ℝ := ∑ t ∈ range (m + 2), (-1 : ℝ) ^ t * renH n m (p + t)

/-- The renewal square `U^m_n` (Toeplitz + Hankel form). -/
def renU (n m i j : ℕ) : ℝ :=
  if i < n ∧ j < n then
    renA n m (i - j + (j - i) + 1) + renA n m (min (i + j + 2) (2 * n - (i + j)))
  else 0

/-- Run totals of the renewal square. -/
def renR (n m s : ℕ) : ℝ := ∑ i ∈ range n, renU n m i (i + s)

/-- The all-ones square of the `n`-box. -/
def boxJ (n i j : ℕ) : ℝ := if i < n ∧ j < n then 1 else 0

/-! ## The weights `H` and the tails `A` -/

theorem renH_of_gt {n m ℓ : ℕ} (h : m + 1 < ℓ) : renH n m ℓ = 0 := by
  unfold renH
  rw [if_neg (by omega)]

theorem alt_sum_add (f : ℕ → ℝ) (p L : ℕ) :
    ∑ t ∈ range (L + 1), (-1 : ℝ) ^ t * f (p + t) +
      ∑ t ∈ range (L + 1), (-1 : ℝ) ^ t * f (p + 1 + t) = f p + (-1) ^ L * f (p + 1 + L) := by
  rw [Finset.sum_range_succ' (fun t => (-1 : ℝ) ^ t * f (p + t)),
    Finset.sum_range_succ (fun t => (-1 : ℝ) ^ t * f (p + 1 + t))]
  have h : ∀ t ∈ range L, (-1 : ℝ) ^ (t + 1) * f (p + (t + 1)) = -((-1) ^ t * f (p + 1 + t)) := by
    intro t _
    rw [pow_succ, show p + (t + 1) = p + 1 + t by omega]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib]
  simp only [pow_zero, one_mul, Nat.add_zero]
  ring

/-- `A(p) + A(p+1) = H(p)`. -/
theorem renA_add (n m p : ℕ) : renA n m p + renA n m (p + 1) = renH n m p := by
  have h := alt_sum_add (renH n m) p (m + 1)
  rw [renH_of_gt (by omega : m + 1 < p + 1 + (m + 1)), mul_zero, add_zero] at h
  exact h

theorem renA_of_ge {n m p : ℕ} (hp : m + 2 ≤ p) : renA n m p = 0 := by
  unfold renA
  exact Finset.sum_eq_zero (fun t _ => by rw [renH_of_gt (by omega), mul_zero])

section Bounds

variable {n m : ℕ} (hm : m + 2 ≤ n)

include hm in
theorem renK_ge_one : 1 ≤ renK n m := by
  unfold renK
  have : (m : ℝ) + 2 ≤ n := by exact_mod_cast hm
  linarith

include hm in
theorem renH_nonneg (ℓ : ℕ) : 0 ≤ renH n m ℓ := by
  unfold renH
  split_ifs with h
  · have hK := renK_ge_one hm
    have hℓ : (ℓ : ℝ) ≤ m + 1 := by exact_mod_cast h.2
    have hx : renK n m ≤ (n : ℝ) - ℓ := by unfold renK; linarith
    have hpos : 0 < ((n : ℝ) - ℓ) * ((n : ℝ) - ℓ + 1) := mul_pos (by linarith) (by linarith)
    have hKx : renK n m * renK n m ≤ ((n : ℝ) - ℓ) * ((n : ℝ) - ℓ) :=
      mul_le_mul hx hx (by linarith) (by linarith)
    have : renK n m ^ 2 / (((n : ℝ) - ℓ) * ((n : ℝ) - ℓ + 1)) ≤ 1 := by
      rw [div_le_one hpos]
      nlinarith
    linarith
  · exact le_rfl

include hm in
theorem renH_le_one (ℓ : ℕ) : renH n m ℓ ≤ 1 := by
  unfold renH
  split_ifs with h
  · have hK := renK_ge_one hm
    have hℓ : (ℓ : ℝ) ≤ m + 1 := by exact_mod_cast h.2
    have hx : renK n m ≤ (n : ℝ) - ℓ := by unfold renK; linarith
    have hpos : 0 < ((n : ℝ) - ℓ) * ((n : ℝ) - ℓ + 1) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ renK n m ^ 2 / (((n : ℝ) - ℓ) * ((n : ℝ) - ℓ + 1)) :=
      div_nonneg (sq_nonneg _) hpos.le
    linarith
  · norm_num

include hm in
theorem renH_anti {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : renH n m (ℓ + 1) ≤ renH n m ℓ := by
  by_cases h : ℓ + 1 ≤ m + 1
  · unfold renH
    rw [if_pos (by omega), if_pos (by omega)]
    have hK := renK_ge_one hm
    have hℓ' : (ℓ : ℝ) + 1 ≤ m + 1 := by exact_mod_cast h
    have hx : renK n m + 1 ≤ (n : ℝ) - ℓ := by unfold renK; linarith
    push_cast
    have h1 : 0 < ((n : ℝ) - (ℓ + 1)) * ((n : ℝ) - (ℓ + 1) + 1) :=
      mul_pos (by linarith) (by linarith)
    have h3 : renK n m ^ 2 / (((n : ℝ) - ℓ) * ((n : ℝ) - ℓ + 1)) ≤
        renK n m ^ 2 / (((n : ℝ) - (ℓ + 1)) * ((n : ℝ) - (ℓ + 1) + 1)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) h1 (by nlinarith)
    linarith
  · rw [renH_of_gt (by omega)]
    exact renH_nonneg hm ℓ

include hm in
/-- `0 ≤ A(p) + A(p+2k+1) = ∑_{t ≤ 2k} (-1)^t H(p+t) ≤ H(p)`. -/
theorem renB_bounds : ∀ k p, 1 ≤ p →
    0 ≤ renA n m p + renA n m (p + 2 * k + 1) ∧
      renA n m p + renA n m (p + 2 * k + 1) ≤ renH n m p := by
  intro k
  induction k with
  | zero =>
    intro p _
    rw [show p + 2 * 0 + 1 = p + 1 by omega, renA_add]
    exact ⟨renH_nonneg hm p, le_rfl⟩
  | succ k ih =>
    intro p hp
    obtain ⟨h1, h2⟩ := ih (p + 2) (by omega)
    have a1 := renA_add n m p
    have a2 := renA_add n m (p + 1)
    rw [show p + 1 + 1 = p + 2 by omega] at a2
    have e : renA n m p + renA n m (p + 2 * (k + 1) + 1) =
        renH n m p - renH n m (p + 1) + (renA n m (p + 2) + renA n m (p + 2 + 2 * k + 1)) := by
      rw [show p + 2 * (k + 1) + 1 = p + 2 + 2 * k + 1 by omega]
      linarith
    have hA1 := renH_anti hm (show 1 ≤ p by omega)
    have hA2 := renH_anti hm (show 1 ≤ p + 1 by omega)
    rw [show p + 1 + 1 = p + 2 by omega] at hA2
    rw [e]
    constructor <;> linarith

end Bounds

/-! ## Cells -/

theorem renU_symm (n m i j : ℕ) : renU n m i j = renU n m j i := by
  unfold renU
  rw [show j - i + (i - j) = i - j + (j - i) by omega, show j + i = i + j by omega]
  by_cases h : i < n ∧ j < n
  · rw [if_pos h, if_pos (And.intro h.2 h.1)]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]

theorem renU_zero {n m i : ℕ} (j : ℕ) (hi : n ≤ i) : renU n m i j = 0 := by
  unfold renU
  rw [if_neg (by omega)]

/-- Closed form: `U(i, j) = A(s+1) + A(s+2k+2)`, `s = |i-j|`, `k = min(i, j, n-1-i, n-1-j)`. -/
theorem renU_eq {n m i j : ℕ} (hi : i < n) (hj : j < n) :
    renU n m i j = renA n m (i - j + (j - i) + 1) +
      renA n m (i - j + (j - i) + 1 + 2 * min (min i j) (n - 1 - max i j) + 1) := by
  unfold renU
  rw [if_pos (And.intro hi hj), show min (i + j + 2) (2 * n - (i + j)) =
    i - j + (j - i) + 1 + 2 * min (min i j) (n - 1 - max i j) + 1 by omega]

theorem renU_band {n m i j : ℕ} (h : m < i - j + (j - i)) : renU n m i j = 0 := by
  by_cases hij : i < n ∧ j < n
  · have h1 : renA n m (i - j + (j - i) + 1) = 0 := renA_of_ge (by omega)
    have h2 : renA n m (i - j + (j - i) + 1 + 2 * min (min i j) (n - 1 - max i j) + 1) = 0 :=
      renA_of_ge (by omega)
    rw [renU_eq hij.1 hij.2, h1, h2, add_zero]
  · unfold renU
    rw [if_neg hij]

section Cells

variable {n m : ℕ} (hm : m + 2 ≤ n)

include hm in
theorem renU_nonneg (i j : ℕ) : 0 ≤ renU n m i j := by
  by_cases h : i < n ∧ j < n
  · rw [renU_eq h.1 h.2]
    exact (renB_bounds hm _ _ (by omega)).1
  · unfold renU
    rw [if_neg h]

include hm in
theorem renU_le_one (i j : ℕ) : renU n m i j ≤ 1 := by
  by_cases h : i < n ∧ j < n
  · rw [renU_eq h.1 h.2]
    exact (renB_bounds hm _ _ (by omega)).2.trans (renH_le_one hm _)
  · unfold renU
    rw [if_neg h]
    norm_num

end Cells

/-! ## Rows -/

theorem renU_row_zero {n m : ℕ} (hn : 0 < n) :
    ∑ j ∈ range n, renU n m 0 j = ∑ j ∈ range n, renH n m (j + 1) := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  unfold renU
  rw [if_pos (And.intro hn hj), show 0 - j + (j - 0) + 1 = j + 1 by omega,
    show min (0 + j + 2) (2 * n - (0 + j)) = j + 1 + 1 by omega, renA_add]

/-- Shifting a row by one: the Toeplitz part gains `A(r+2) - A(n-r)`, the Hankel part loses it. -/
theorem renU_row_succ (n m r : ℕ) (hr : r + 1 < n) :
    ∑ j ∈ range n, renU n m (r + 1) j = ∑ j ∈ range n, renU n m r j := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have e1 : ∀ r', r' < N + 1 → ∑ j ∈ range (N + 1), renU (N + 1) m r' j =
      ∑ j ∈ range (N + 1), renA (N + 1) m (r' - j + (j - r') + 1) +
        ∑ j ∈ range (N + 1), renA (N + 1) m (min (r' + j + 2) (2 * (N + 1) - (r' + j))) := by
    intro r' hr'
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    unfold renU
    rw [if_pos (And.intro hr' (Finset.mem_range.1 hj))]
  rw [e1 (r + 1) hr, e1 r (by omega)]
  have hT1 : ∑ j ∈ range (N + 1), renA (N + 1) m (r + 1 - j + (j - (r + 1)) + 1) =
      ∑ j ∈ range N, renA (N + 1) m (r - j + (j - r) + 1) + renA (N + 1) m (r + 2) := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      omega
    · congr 1
      omega
  have hT0 : ∑ j ∈ range (N + 1), renA (N + 1) m (r - j + (j - r) + 1) =
      ∑ j ∈ range N, renA (N + 1) m (r - j + (j - r) + 1) + renA (N + 1) m (N + 1 - r) := by
    rw [Finset.sum_range_succ]
    congr 2
    omega
  have hH1 : ∑ j ∈ range (N + 1),
      renA (N + 1) m (min (r + 1 + j + 2) (2 * (N + 1) - (r + 1 + j))) =
      ∑ j ∈ range N, renA (N + 1) m (min (r + (j + 1) + 2) (2 * (N + 1) - (r + (j + 1)))) +
        renA (N + 1) m (N + 1 - r) := by
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      omega
    · congr 1
      omega
  have hH0 : ∑ j ∈ range (N + 1), renA (N + 1) m (min (r + j + 2) (2 * (N + 1) - (r + j))) =
      ∑ j ∈ range N, renA (N + 1) m (min (r + (j + 1) + 2) (2 * (N + 1) - (r + (j + 1)))) +
        renA (N + 1) m (r + 2) := by
    rw [Finset.sum_range_succ']
    congr 2
    omega
  rw [hT1, hT0, hH1, hH0]
  ring

theorem renU_row_const (n m : ℕ) : ∀ r, r < n →
    ∑ j ∈ range n, renU n m r j = ∑ j ∈ range n, renU n m 0 j := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
    intro hr
    rw [renU_row_succ n m r hr, ih (by omega)]

section Sums

variable {n m : ℕ} (hm : m + 2 ≤ n)

include hm in
/-- `∑_ℓ H(ℓ) = (m+1) - K + K²/n = (m+1)²/n`. -/
theorem sum_renH : ∑ j ∈ range n, renH n m (j + 1) = ((m : ℝ) + 1) ^ 2 / n := by
  have hsplit : ∑ j ∈ range n, renH n m (j + 1) = ∑ j ∈ range (m + 1), renH n m (j + 1) := by
    have hz : ∑ j ∈ Ico (m + 1) n, renH n m (j + 1) = 0 :=
      Finset.sum_eq_zero (fun j hj => renH_of_gt (by rw [Finset.mem_Ico] at hj; omega))
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ n), hz, add_zero]
  have hK := renK_ge_one hm
  set g : ℕ → ℝ := fun q => 1 / ((n : ℝ) - q) with hg
  have hterm : ∀ j ∈ range (m + 1), renH n m (j + 1) = 1 - renK n m ^ 2 * (g (j + 1) - g j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold renH
    rw [if_pos (by omega)]
    have hj' : (j : ℝ) + 1 ≤ m + 1 := by exact_mod_cast (show j + 1 ≤ m + 1 by omega)
    have hx : renK n m ≤ (n : ℝ) - (j + 1) := by unfold renK; linarith
    have h1 : (n : ℝ) - (j + 1) ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (j + 1)).ne'
    have h2 : (n : ℝ) - (j + 1) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (j + 1) + 1).ne'
    have h3 : (n : ℝ) - j ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - j).ne'
    simp only [hg]
    push_cast
    field_simp
    ring
  rw [hsplit, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub g (m + 1)]
  simp only [hg, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_zero,
    sub_zero]
  unfold renK
  have hn : (m : ℝ) + 2 ≤ n := by exact_mod_cast hm
  have h1 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  have h2 : (n : ℝ) - (m + 1) ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (m + 1)).ne'
  push_cast
  field_simp
  ring

include hm in
theorem renU_row {r : ℕ} (hr : r < n) :
    ∑ j ∈ range n, renU n m r j = ((m : ℝ) + 1) ^ 2 / n := by
  rw [renU_row_const n m r hr, renU_row_zero (by omega), sum_renH hm]

end Sums

/-! ## Runs -/

theorem renR_eq_short (n m s : ℕ) : renR n m s = ∑ i ∈ range (n - s), renU n m i (i + s) := by
  unfold renR
  have hz : ∑ i ∈ Ico (n - s) n, renU n m i (i + s) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [renU_symm]
    exact renU_zero _ (by omega)
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le n s), hz, add_zero]

/-- Run recurrence `R(s) = W(s+1) + R(s+2)`. -/
theorem renR_rec {n m s : ℕ} (hs : s + 2 ≤ n) :
    renR n m s = 2 * renH n m (s + 1) +
      ((n : ℝ) - s - 2) * (renH n m (s + 1) - renH n m (s + 2)) + renR n m (s + 2) := by
  rw [renR_eq_short, renR_eq_short]
  obtain ⟨M, hM⟩ : ∃ M, n - s = M + 2 := ⟨n - s - 2, by omega⟩
  have hM2 : n - (s + 2) = M := by omega
  have hMr : ((n : ℝ) - s - 2) = M := by
    have e : n = M + s + 2 := by omega
    rw [e]
    push_cast
    ring
  rw [hM2, hM, hMr, Finset.sum_range_succ', Finset.sum_range_succ]
  have hterm : ∀ i ∈ range M, renU n m (i + 1) (i + 1 + s) =
      renU n m i (i + (s + 2)) + (renA n m (s + 1) - renA n m (s + 3)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold renU
    rw [if_pos (by omega), if_pos (by omega),
      show i + 1 - (i + 1 + s) + (i + 1 + s - (i + 1)) + 1 = s + 1 by omega,
      show i - (i + (s + 2)) + (i + (s + 2) - i) + 1 = s + 3 by omega,
      show min (i + 1 + (i + 1 + s) + 2) (2 * n - (i + 1 + (i + 1 + s))) =
        min (i + (i + (s + 2)) + 2) (2 * n - (i + (i + (s + 2)))) by omega]
    ring
  have e0 : renU n m 0 (0 + s) = renA n m (s + 1) + renA n m (s + 2) := by
    unfold renU
    rw [if_pos (by omega), show 0 - (0 + s) + (0 + s - 0) + 1 = s + 1 by omega,
      show min (0 + (0 + s) + 2) (2 * n - (0 + (0 + s))) = s + 2 by omega]
  have eM : renU n m (M + 1) (M + 1 + s) = renA n m (s + 1) + renA n m (s + 2) := by
    unfold renU
    rw [if_pos (by omega),
      show M + 1 - (M + 1 + s) + (M + 1 + s - (M + 1)) + 1 = s + 1 by omega,
      show min (M + 1 + (M + 1 + s) + 2) (2 * n - (M + 1 + (M + 1 + s))) = s + 2 by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, e0, eM, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have a1 := renA_add n m (s + 1)
  have a2 := renA_add n m (s + 2)
  rw [show s + 1 + 1 = s + 2 by omega] at a1
  rw [show s + 2 + 1 = s + 3 by omega] at a2
  have hdiff : renA n m (s + 1) - renA n m (s + 3) = renH n m (s + 1) - renH n m (s + 2) := by
    linarith
  rw [hdiff]
  linarith

section Runs

variable {n m : ℕ} (hm : m + 2 ≤ n)

include hm in
theorem renW_two {s : ℕ} (h : s + 1 ≤ m) :
    2 * renH n m (s + 1) + ((n : ℝ) - s - 2) * (renH n m (s + 1) - renH n m (s + 2)) = 2 := by
  unfold renH
  rw [if_pos (by omega), if_pos (by omega)]
  have hK := renK_ge_one hm
  have hs : (s : ℝ) + 1 ≤ m := by exact_mod_cast h
  have hx : renK n m + 2 ≤ (n : ℝ) - s := by unfold renK; linarith
  push_cast
  have h1 : (n : ℝ) - (s + 1) ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (s + 1)).ne'
  have h2 : (n : ℝ) - (s + 1) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (s + 1) + 1).ne'
  have h3 : (n : ℝ) - (s + 2) ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (s + 2)).ne'
  have h4 : (n : ℝ) - (s + 2) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (s + 2) + 1).ne'
  field_simp
  ring

include hm in
theorem renW_one :
    2 * renH n m (m + 1) + ((n : ℝ) - m - 2) * (renH n m (m + 1) - renH n m (m + 2)) = 1 := by
  rw [renH_of_gt (show m + 1 < m + 2 by omega)]
  unfold renH
  rw [if_pos (by omega)]
  unfold renK
  have hn : (m : ℝ) + 2 ≤ n := by exact_mod_cast hm
  push_cast
  have h1 : (n : ℝ) - (m + 1) ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (m + 1)).ne'
  have h2 : (n : ℝ) - (m + 1) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - (m + 1) + 1).ne'
  field_simp
  ring

include hm in
theorem renR_eq : ∀ q s, m + 1 ≤ s + q →
    renR n m s = if s ≤ m then (m : ℝ) + 1 - s else 0 := by
  intro q
  induction q with
  | zero =>
    intro s hs
    rw [if_neg (by omega)]
    exact Finset.sum_eq_zero (fun i _ => renU_band (by omega))
  | succ q ih =>
    intro s hs
    by_cases hsm : s ≤ m
    · rw [if_pos hsm, renR_rec (show s + 2 ≤ n by omega), ih (s + 2) (by omega)]
      by_cases h1 : s + 1 ≤ m
      · rw [renW_two hm h1]
        by_cases h2 : s + 2 ≤ m
        · rw [if_pos h2]
          push_cast
          ring
        · rw [if_neg h2]
          have e : (m : ℝ) = s + 1 := by exact_mod_cast (show m = s + 1 by omega)
          rw [e]
          ring
      · have e : s = m := by omega
        rw [if_neg (by omega), e, renW_one hm]
        ring
    · rw [if_neg hsm]
      exact Finset.sum_eq_zero (fun i _ => renU_band (by omega))

end Runs

/-! ## Interval uniformisations -/

/-- **The renewal square `U^m_n` is an interval uniformisation of `[0, m]`** (`m ≤ n - 2`). -/
theorem isIntervalUnif_renU {n m : ℕ} (hm : m + 2 ≤ n) : IsIntervalUnif n 0 m (renU n m) :=
  { symm := renU_symm n m
    nonneg := renU_nonneg hm
    le_one := renU_le_one hm
    zero := fun _ j hi => renU_zero j hi
    run := fun s => by
      show renR n m s = _
      rw [renR_eq hm (m + 1) s (by omega), card_filter_Icc_le]
      split_ifs with h
      · rw [show m + 1 - max 0 s = m + 1 - s by omega, Nat.cast_sub (by omega)]
        push_cast
        ring
      · rw [show m + 1 - max 0 s = 0 by omega]
        simp
    row := fun r hr => by
      rw [renU_row hm hr, sum_Icc_odd (by omega)]
      push_cast
      ring }

/-- The all-ones square is an interval uniformisation of `[0, n-1]`. -/
theorem isIntervalUnif_boxJ {n : ℕ} (hn : 0 < n) : IsIntervalUnif n 0 (n - 1) (boxJ n) :=
  { symm := fun i j => by
      unfold boxJ
      split_ifs <;> first | rfl | (exfalso; omega)
    nonneg := fun i j => by
      unfold boxJ
      split_ifs <;> norm_num
    le_one := fun i j => by
      unfold boxJ
      split_ifs <;> norm_num
    zero := fun i j hi => by
      unfold boxJ
      rw [if_neg (by omega)]
    run := fun s => by
      have e : ∀ i ∈ range n, boxJ n i (i + s) = if i < n - s then 1 else 0 := by
        intro i hi
        rw [Finset.mem_range] at hi
        unfold boxJ
        by_cases h : i < n - s
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [Finset.sum_congr rfl e, sum_range_indicator, card_filter_Icc_le,
        show min n (n - s) = n - 1 + 1 - max 0 s by omega]
    row := fun r hr => by
      have e : ∀ j ∈ range n, boxJ n r j = 1 := fun j hj => by
        unfold boxJ
        rw [if_pos (And.intro hr (Finset.mem_range.1 hj))]
      have hc : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast (show n - 1 + 1 = n by omega)
      have hn' : (n : ℝ) ≠ 0 := (by exact_mod_cast hn : (0 : ℝ) < n).ne'
      rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        sum_Icc_odd (by omega), hc]
      push_cast
      field_simp
      ring }

/-- **Complement**: `J - u` is an interval uniformisation of `[m+1, n-1]` if `u` is one of
`[0, m]`. -/
theorem IsIntervalUnif.compl {n m : ℕ} {u : ℕ → ℕ → ℝ} (hu : IsIntervalUnif n 0 m u)
    (hmn : m + 2 ≤ n) : IsIntervalUnif n (m + 1) (n - 1) (fun i j => boxJ n i j - u i j) := by
  have hJ := isIntervalUnif_boxJ (show 0 < n by omega)
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j hi => ?_, fun s => ?_,
    fun r hr => ?_⟩
  · show boxJ n i j - u i j = boxJ n j i - u j i
    rw [hJ.symm i j, hu.symm i j]
  · show 0 ≤ boxJ n i j - u i j
    by_cases h : i < n ∧ j < n
    · have h1 : boxJ n i j = 1 := by
        unfold boxJ
        rw [if_pos h]
      rw [h1]
      linarith [hu.le_one i j]
    · have h1 : boxJ n i j = 0 := by
        unfold boxJ
        rw [if_neg h]
      have h2 : u i j = 0 := by
        by_cases hi : n ≤ i
        · exact hu.zero i j hi
        · exact hu.zero' i j (by omega)
      rw [h1, h2, sub_zero]
  · show boxJ n i j - u i j ≤ 1
    linarith [hJ.le_one i j, hu.nonneg i j]
  · show boxJ n i j - u i j = 0
    rw [hJ.zero i j hi, hu.zero i j hi, sub_zero]
  · show ∑ i ∈ range n, (boxJ n i (i + s) - u i (i + s)) = _
    rw [Finset.sum_sub_distrib, hJ.run s, hu.run s, card_filter_Icc_le, card_filter_Icc_le,
      card_filter_Icc_le,
      show n - 1 + 1 - max 0 s = (m + 1 - max 0 s) + (n - 1 + 1 - max (m + 1) s) by omega,
      Nat.cast_add]
    ring
  · show ∑ j ∈ range n, (boxJ n r j - u r j) = _
    have hc : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast (show n - 1 + 1 = n by omega)
    rw [Finset.sum_sub_distrib, hJ.row r hr, hu.row r hr, sum_Icc_odd (by omega),
      sum_Icc_odd (by omega), sum_Icc_odd (by omega), hc]
    push_cast
    ring

end STUProof
