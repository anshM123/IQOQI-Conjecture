import STUProof.Renewal

/-!
# The cross construction for general intervals

For `1 ≤ lo ≤ hi ≤ n - 2`, P-UNIF (`iqoqi/programs/unif/LOG.md`, "HALF construction") uses
  `X = θ U^hi_n + (1-θ) avg_t J[W_t] - ½ U^{lo-1}_n - ½ avg_t U^{lo-1}_b[W_t]`,
with `b = hi + 1`, the windows `W_t = [t, t + hi]` (`t = 0, …, n - b`, uniform weights), `J[W]` the
all-ones square on `W`, `V[W]` a `b`-box configuration placed on `W`, and `θ = 1 - lo²/(2b²)`.

Proved here (`isIntervalUnif_crossX`): `X` is symmetric, zero off the box, `X ≤ 1`, its runs are
`#{a ∈ [lo, hi] : s ≤ a}` and its rows `((hi+1)² - lo²)/n` (the window-coverage terms cancel since
`(1-θ) b = lo²/(2b)`), and `X ≥ 0` on the runs `s ≥ lo` (there the two renewal squares vanish).
Nonnegativity on the short runs `s < lo` is the single remaining inequality `XShortNonneg n lo hi`
(verified exactly for all `n ≤ 76` by P-UNIF); given it, `X` is an interval uniformisation of
`[lo, hi]`.
-/

open Finset

noncomputable section

namespace STUProof

/-! ## Placing a configuration on a window -/

/-- `V` placed at offset `t`: the cell `(i, j)` gets `V (i - t) (j - t)` for `i, j ≥ t`. -/
def place (t : ℕ) (V : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if t ≤ i ∧ t ≤ j then V (i - t) (j - t) else 0

/-- Average of the placements at the offsets `t = 0, …, T-1`. -/
def avgPlace (T : ℕ) (V : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := (∑ t ∈ range T, place t V i j) / T

/-- Number of windows `[t, t+b)`, `t < T`, containing the point `r`. -/
def covW (T b r : ℕ) : ℝ := ∑ t ∈ range T, if t ≤ r ∧ r - t < b then (1 : ℝ) else 0

section Place

variable {b lo' hi' : ℕ} {V : ℕ → ℕ → ℝ}

theorem place_symm (hV : IsIntervalUnif b lo' hi' V) (t i j : ℕ) :
    place t V i j = place t V j i := by
  unfold place
  by_cases h : t ≤ i ∧ t ≤ j
  · rw [if_pos h, if_pos (And.intro h.2 h.1), hV.symm]
  · rw [if_neg h, if_neg (fun h' => h (And.intro h'.2 h'.1))]

theorem place_nonneg (hV : IsIntervalUnif b lo' hi' V) (t i j : ℕ) : 0 ≤ place t V i j := by
  unfold place
  split_ifs
  · exact hV.nonneg _ _
  · exact le_rfl

theorem place_le_one (hV : IsIntervalUnif b lo' hi' V) (t i j : ℕ) : place t V i j ≤ 1 := by
  unfold place
  split_ifs
  · exact hV.le_one _ _
  · norm_num

theorem place_zero (hV : IsIntervalUnif b lo' hi' V) {t n i : ℕ} (htb : t + b ≤ n) (j : ℕ)
    (hi : n ≤ i) : place t V i j = 0 := by
  unfold place
  split_ifs
  · exact hV.zero _ _ (by omega)
  · rfl

/-- Runs of a placed configuration are the runs of the configuration. -/
theorem place_run (hV : IsIntervalUnif b lo' hi' V) {t n : ℕ} (htb : t + b ≤ n) (s : ℕ) :
    ∑ i ∈ range n, place t V i (i + s) = ∑ i ∈ range b, V i (i + s) := by
  have h0 : ∑ i ∈ range t, place t V i (i + s) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    unfold place
    rw [if_neg (by omega)]
  have h1 : ∀ k ∈ range (n - t), place t V (t + k) (t + k + s) = V k (k + s) := by
    intro k _
    unfold place
    rw [if_pos (by omega), show t + k - t = k by omega, show t + k + s - t = k + s by omega]
  have hz : ∑ k ∈ Ico b (n - t), V k (k + s) = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_Ico] at hk
    exact hV.zero _ _ hk.1
  rw [← Finset.sum_range_add_sum_Ico _ (show t ≤ n by omega), h0, zero_add,
    Finset.sum_Ico_eq_sum_range, Finset.sum_congr rfl h1,
    ← Finset.sum_range_add_sum_Ico _ (show b ≤ n - t by omega), hz, add_zero]

/-- Rows of a placed configuration. -/
theorem place_row (hV : IsIntervalUnif b lo' hi' V) {t n : ℕ} (htb : t + b ≤ n) (r : ℕ) :
    ∑ j ∈ range n, place t V r j =
      if t ≤ r ∧ r - t < b then (∑ a ∈ Icc lo' hi', (2 * (a : ℝ) + 1)) / b else 0 := by
  by_cases hr : t ≤ r
  · have h0 : ∑ j ∈ range t, place t V r j = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      unfold place
      rw [if_neg (by omega)]
    have h1 : ∀ k ∈ range (n - t), place t V r (t + k) = V (r - t) k := by
      intro k _
      unfold place
      rw [if_pos (by omega), show t + k - t = k by omega]
    have hz : ∑ k ∈ Ico b (n - t), V (r - t) k = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      rw [Finset.mem_Ico] at hk
      exact hV.zero' _ _ hk.1
    rw [← Finset.sum_range_add_sum_Ico _ (show t ≤ n by omega), h0, zero_add,
      Finset.sum_Ico_eq_sum_range, Finset.sum_congr rfl h1,
      ← Finset.sum_range_add_sum_Ico _ (show b ≤ n - t by omega), hz, add_zero,
      hV.row' (r - t) b le_rfl]
    by_cases h2 : r - t < b
    · rw [if_pos h2, if_pos (And.intro hr h2)]
    · rw [if_neg h2, if_neg (fun h' => h2 h'.2)]
  · rw [if_neg (fun h' => hr h'.1)]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    unfold place
    rw [if_neg (by omega)]

/-- A placed configuration vanishes where `V` vanishes by its band. -/
theorem place_band {m : ℕ} (hband : ∀ i j, m < Nat.dist i j → V i j = 0) (t : ℕ) {i j : ℕ}
    (h : m < Nat.dist i j) : place t V i j = 0 := by
  unfold place
  split_ifs with h'
  · exact hband _ _ (by unfold Nat.dist at h ⊢; omega)
  · rfl

end Place

section Avg

variable {b lo' hi' : ℕ} {V : ℕ → ℕ → ℝ}

theorem avgPlace_symm (hV : IsIntervalUnif b lo' hi' V) (T i j : ℕ) :
    avgPlace T V i j = avgPlace T V j i := by
  unfold avgPlace
  rw [Finset.sum_congr rfl (fun t _ => place_symm hV t i j)]

theorem avgPlace_nonneg (hV : IsIntervalUnif b lo' hi' V) (T i j : ℕ) : 0 ≤ avgPlace T V i j :=
  div_nonneg (Finset.sum_nonneg (fun t _ => place_nonneg hV t i j)) (Nat.cast_nonneg T)

theorem avgPlace_le_one (hV : IsIntervalUnif b lo' hi' V) {T : ℕ} (hT : 0 < T) (i j : ℕ) :
    avgPlace T V i j ≤ 1 := by
  unfold avgPlace
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [div_le_one hT']
  calc ∑ t ∈ range T, place t V i j ≤ ∑ _t ∈ range T, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => place_le_one hV t i j)
    _ = T := by simp

theorem avgPlace_zero (hV : IsIntervalUnif b lo' hi' V) {n i : ℕ} (hbn : b ≤ n) (j : ℕ)
    (hi : n ≤ i) : avgPlace (n + 1 - b) V i j = 0 := by
  unfold avgPlace
  rw [Finset.sum_eq_zero (fun t ht => place_zero hV
    (by rw [Finset.mem_range] at ht; omega) j hi), zero_div]

theorem avgPlace_band {m : ℕ} (hband : ∀ i j, m < Nat.dist i j → V i j = 0) (T : ℕ) {i j : ℕ}
    (h : m < Nat.dist i j) : avgPlace T V i j = 0 := by
  unfold avgPlace
  rw [Finset.sum_eq_zero (fun t _ => place_band hband t h), zero_div]

/-- Runs of the window average are the runs of `V`. -/
theorem avgPlace_run (hV : IsIntervalUnif b lo' hi' V) {n : ℕ} (hbn : b ≤ n) (s : ℕ) :
    ∑ i ∈ range n, avgPlace (n + 1 - b) V i (i + s) =
      (((Icc lo' hi').filter (fun a => s ≤ a)).card : ℝ) := by
  unfold avgPlace
  have hT : ((n + 1 - b : ℕ) : ℝ) ≠ 0 := by
    have : 0 < n + 1 - b := by omega
    exact_mod_cast this.ne'
  have e : ∀ t ∈ range (n + 1 - b), ∑ i ∈ range n, place t V i (i + s) =
      (((Icc lo' hi').filter (fun a => s ≤ a)).card : ℝ) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [place_run hV (by omega) s, hV.run' s b (Nat.sub_le b s)]
  rw [← Finset.sum_div, Finset.sum_comm, Finset.sum_congr rfl e, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hT

/-- Rows of the window average: `covW` times the row sum of `V`, divided by the window count. -/
theorem avgPlace_row (hV : IsIntervalUnif b lo' hi' V) {n : ℕ} (hbn : b ≤ n) (r : ℕ) :
    ∑ j ∈ range n, avgPlace (n + 1 - b) V r j =
      covW (n + 1 - b) b r * ((∑ a ∈ Icc lo' hi', (2 * (a : ℝ) + 1)) / b) / (n + 1 - b : ℕ) := by
  unfold avgPlace covW
  rw [← Finset.sum_div, Finset.sum_comm, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  rw [place_row hV (show t + b ≤ n by omega) r]
  split_ifs <;> ring

end Avg

/-! ## The construction -/

/-- `θ = 1 - lo²/(2 (hi+1)²)`. -/
def crossTheta (lo hi : ℕ) : ℝ := 1 - (lo : ℝ) ^ 2 / (2 * ((hi : ℝ) + 1) ^ 2)

/-- The cross construction `X(n, lo, hi)` (P-UNIF), with windows of size `b = hi + 1` at the
`n - hi` offsets `t = 0, …, n - b`. -/
def crossX (n lo hi i j : ℕ) : ℝ :=
  crossTheta lo hi * renU n hi i j +
    (1 - crossTheta lo hi) * avgPlace (n + 1 - (hi + 1)) (boxJ (hi + 1)) i j -
    1 / 2 * renU n (lo - 1) i j -
    1 / 2 * avgPlace (n + 1 - (hi + 1)) (renU (hi + 1) (lo - 1)) i j

/-- **The open inequality**: `X(n, lo, hi) ≥ 0` on the short runs `|i - j| < lo`. -/
def XShortNonneg (n lo hi : ℕ) : Prop :=
  ∀ i j, i < n → j < n → Nat.dist i j < lo → 0 ≤ crossX n lo hi i j

theorem crossTheta_bounds {lo hi : ℕ} (h : lo ≤ hi) :
    0 ≤ crossTheta lo hi ∧ crossTheta lo hi ≤ 1 := by
  unfold crossTheta
  have hb : (0 : ℝ) < ((hi : ℝ) + 1) := by positivity
  have hl : (lo : ℝ) ≤ hi + 1 := by
    have : (lo : ℝ) ≤ hi := by exact_mod_cast h
    linarith
  have h0 : (0 : ℝ) ≤ lo := Nat.cast_nonneg lo
  have hpos : 0 < 2 * ((hi : ℝ) + 1) ^ 2 := by positivity
  constructor
  · have hsq := mul_le_mul hl hl h0 hb.le
    have : (lo : ℝ) ^ 2 / (2 * ((hi : ℝ) + 1) ^ 2) ≤ 1 := by
      rw [div_le_one hpos]
      nlinarith
    linarith
  · have : 0 ≤ (lo : ℝ) ^ 2 / (2 * ((hi : ℝ) + 1) ^ 2) := by positivity
    linarith

section Cross

variable {n lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi + 2 ≤ n)

include hlo hlohi in
theorem crossX_symm (i j : ℕ) : crossX n lo hi i j = crossX n lo hi j i := by
  have hJ := isIntervalUnif_boxJ (show 0 < hi + 1 by omega)
  have hV := isIntervalUnif_renU (show lo - 1 + 2 ≤ hi + 1 by omega)
  unfold crossX
  rw [renU_symm n hi i j, renU_symm n (lo - 1) i j, avgPlace_symm hJ, avgPlace_symm hV]

include hlo hlohi hhi in
theorem crossX_zero {i : ℕ} (j : ℕ) (hi' : n ≤ i) : crossX n lo hi i j = 0 := by
  have hJ := isIntervalUnif_boxJ (show 0 < hi + 1 by omega)
  have hV := isIntervalUnif_renU (show lo - 1 + 2 ≤ hi + 1 by omega)
  unfold crossX
  rw [renU_zero j hi', renU_zero j hi', avgPlace_zero hJ (by omega) j hi',
    avgPlace_zero hV (by omega) j hi']
  ring

include hlo hlohi hhi in
theorem crossX_le_one (i j : ℕ) : crossX n lo hi i j ≤ 1 := by
  have hJ := isIntervalUnif_boxJ (show 0 < hi + 1 by omega)
  have hV := isIntervalUnif_renU (show lo - 1 + 2 ≤ hi + 1 by omega)
  obtain ⟨hθ0, hθ1⟩ := crossTheta_bounds hlohi
  have h1 : crossTheta lo hi * renU n hi i j ≤ crossTheta lo hi * 1 :=
    mul_le_mul_of_nonneg_left (renU_le_one hhi i j) hθ0
  have h2 : (1 - crossTheta lo hi) * avgPlace (n + 1 - (hi + 1)) (boxJ (hi + 1)) i j ≤
      (1 - crossTheta lo hi) * 1 :=
    mul_le_mul_of_nonneg_left (avgPlace_le_one hJ (by omega) i j) (by linarith)
  have h3 := renU_nonneg (show lo - 1 + 2 ≤ n by omega) i j
  have h4 := avgPlace_nonneg hV (n + 1 - (hi + 1)) i j
  unfold crossX
  linarith

include hlo hlohi hhi in
/-- `X ≥ 0` on the long runs `|i - j| ≥ lo`. -/
theorem crossX_nonneg_long {i j : ℕ} (h : lo ≤ Nat.dist i j) : 0 ≤ crossX n lo hi i j := by
  have hJ := isIntervalUnif_boxJ (show 0 < hi + 1 by omega)
  obtain ⟨hθ0, hθ1⟩ := crossTheta_bounds hlohi
  have hL : renU n (lo - 1) i j = 0 := renU_band (by unfold Nat.dist at h; omega)
  have hA : avgPlace (n + 1 - (hi + 1)) (renU (hi + 1) (lo - 1)) i j = 0 :=
    avgPlace_band (m := lo - 1) (fun x y hxy => renU_band (by unfold Nat.dist at hxy; omega)) _
      (by omega)
  unfold crossX
  rw [hL, hA]
  have h1 := mul_nonneg hθ0 (renU_nonneg hhi i j)
  have h2 := mul_nonneg (show 0 ≤ 1 - crossTheta lo hi by linarith)
    (avgPlace_nonneg hJ (n + 1 - (hi + 1)) i j)
  linarith

include hlo hlohi hhi in
theorem crossX_run (s : ℕ) :
    ∑ i ∈ range n, crossX n lo hi i (i + s) =
      (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) := by
  have hU := isIntervalUnif_renU hhi
  have hL := isIntervalUnif_renU (show lo - 1 + 2 ≤ n by omega)
  have hJ := isIntervalUnif_boxJ (show 0 < hi + 1 by omega)
  have hV := isIntervalUnif_renU (show lo - 1 + 2 ≤ hi + 1 by omega)
  unfold crossX
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hU.run s, hL.run s, avgPlace_run hJ (by omega) s, avgPlace_run hV (by omega) s]
  simp only [card_filter_Icc_le]
  rw [show hi + 1 - 1 = hi by omega,
    show hi + 1 - max 0 s = (lo - 1 + 1 - max 0 s) + (hi + 1 - max lo s) by omega, Nat.cast_add]
  ring

include hlo hlohi hhi in
theorem crossX_row {r : ℕ} (hr : r < n) :
    ∑ j ∈ range n, crossX n lo hi r j = (∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1)) / n := by
  have hU := isIntervalUnif_renU hhi
  have hL := isIntervalUnif_renU (show lo - 1 + 2 ≤ n by omega)
  have hJ := isIntervalUnif_boxJ (show 0 < hi + 1 by omega)
  have hV := isIntervalUnif_renU (show lo - 1 + 2 ≤ hi + 1 by omega)
  rw [sum_Icc_odd (show lo ≤ hi + 1 by omega)]
  unfold crossX
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hU.row r hr, hL.row r hr, avgPlace_row hJ (by omega) r, avgPlace_row hV (by omega) r,
    sum_Icc_odd (show 0 ≤ hi + 1 by omega), sum_Icc_odd (show 0 ≤ lo - 1 + 1 by omega),
    sum_Icc_odd (show 0 ≤ hi + 1 - 1 + 1 by omega), show hi + 1 - 1 = hi by omega]
  have hlo' : ((lo - 1 : ℕ) : ℝ) + 1 = lo := by exact_mod_cast (show lo - 1 + 1 = lo by omega)
  rw [hlo']
  unfold crossTheta
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    exact_mod_cast this.ne'
  set T : ℝ := ((n + 1 - (hi + 1) : ℕ) : ℝ) with hTdef
  have hT : T ≠ 0 := by
    have : 0 < n + 1 - (hi + 1) := by omega
    rw [hTdef]
    exact_mod_cast this.ne'
  set C : ℝ := covW (n + 1 - (hi + 1)) (hi + 1) r with hC
  have hb : ((hi : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end Cross

/-- **The cross construction is an interval uniformisation of `[lo, hi]`**, given the short-run
inequality `XShortNonneg n lo hi`. -/
theorem isIntervalUnif_crossX {n lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi + 2 ≤ n)
    (hX : XShortNonneg n lo hi) : IsIntervalUnif n lo hi (crossX n lo hi) :=
  { symm := crossX_symm hlo hlohi
    nonneg := fun i j => by
      by_cases hin : i < n ∧ j < n
      · by_cases hd : Nat.dist i j < lo
        · exact hX i j hin.1 hin.2 hd
        · exact crossX_nonneg_long hlo hlohi hhi (by omega)
      · by_cases hi' : n ≤ i
        · exact le_of_eq (crossX_zero hlo hlohi hhi j hi').symm
        · rw [crossX_symm hlo hlohi]
          exact le_of_eq (crossX_zero hlo hlohi hhi i (by omega)).symm
    le_one := crossX_le_one hlo hlohi hhi
    zero := fun _ j hi' => crossX_zero hlo hlohi hhi j hi'
    run := crossX_run hlo hlohi hhi
    row := fun _ hr => crossX_row hlo hlohi hhi hr }

end STUProof
