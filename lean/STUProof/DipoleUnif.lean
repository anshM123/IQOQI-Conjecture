import STUProof.IntervalUnif

/-!
# The T/H/G construction with at most one dipole

P-PROOF (`iqoqi/programs/proof/LOG.md`, "THE PROOF", Sections 1-2). For functions `T, H, G` the
*T/H/G matrix* of the `n`-box is
  `U(i, j) = (T(|i-j|) + H(m'(i, j)))/2`,  `m'(i, j) = min(i+j+1, 2n-1-i-j)`   (`i + j ≠ n - 1`),
  `U(i, j) = (T(|i-j|) + G(|i-j|))/2`                                            (`i + j = n - 1`).
Generic facts (`thg_*`): symmetry, the two-step run recurrence (Lemma 1.1-1.2), the row shift
identity (Lemma 1.3), and `0 ≤ U ≤ 1` from one-dimensional conditions (Lemma 1.4). A generic
mass count (`row_const_value`) identifies a constant row sum.

The dipole construction (`dipU`): for `1 ≤ lo ≤ hi ≤ n-2`, `K = n-1-hi`, `M = n-lo` and an amplitude
`α` (with `α = 0` or `2 hi ≥ n`), `T(s) = τ(n-s)`, `H(u) = T(u) - α[u = hi]`,
`G(u) = α[u ≤ 2hi-n-1]`, where `τ` is defined in `x = n - s` coordinates by the pair sums
`τ(x) + τ(x-1) = Q(x)/(x(x-1))`, `τ(0) = 0` (Lemma 2.1). Runs and rows hold for every `α`
(`isIntervalUnif_dip`); `0 ≤ U ≤ 1` is reduced to the one-dimensional cell conditions on `τ`.
-/

open Finset

noncomputable section

namespace STUProof

/-! ## Generic T/H/G matrices -/

/-- The T/H/G matrix of the `n`-box. -/
def thgU (n : ℕ) (T H G : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i < n ∧ j < n then
    (T (Nat.dist i j) +
      (if i + j + 1 = n then G (Nat.dist i j) else H (min (i + j + 1) (2 * n - 1 - (i + j))))) / 2
  else 0

/-- The Hankel part as a function of `S = i + j` (zero on the antidiagonal). -/
def thgHk (n : ℕ) (H : ℕ → ℝ) (S : ℕ) : ℝ :=
  if S + 1 = n then 0 else H (min (S + 1) (2 * n - 1 - S))

section Generic

variable {n : ℕ} {T H G : ℕ → ℝ}

theorem thgU_symm (i j : ℕ) : thgU n T H G i j = thgU n T H G j i := by
  unfold thgU
  rw [Nat.dist_comm j i, show j + i = i + j by omega]
  by_cases h : i < n ∧ j < n
  · rw [if_pos h, if_pos (And.intro h.2 h.1)]
  · rw [if_neg h, if_neg (fun h' => h (And.intro h'.2 h'.1))]

theorem thgU_zero {i : ℕ} (j : ℕ) (hi : n ≤ i) : thgU n T H G i j = 0 := by
  unfold thgU
  rw [if_neg (by omega)]

theorem thgU_off {i j : ℕ} (hi : i < n) (hj : j < n) (h : ¬ (i + j + 1 = n)) :
    thgU n T H G i j = (T (Nat.dist i j) + H (min (i + j + 1) (2 * n - 1 - (i + j)))) / 2 := by
  unfold thgU
  rw [if_pos (And.intro hi hj), if_neg h]

theorem thgU_anti {i j : ℕ} (hi : i < n) (hj : j < n) (h : i + j + 1 = n) :
    thgU n T H G i j = (T (Nat.dist i j) + G (Nat.dist i j)) / 2 := by
  unfold thgU
  rw [if_pos (And.intro hi hj), if_pos h]

theorem thg_run_short (s : ℕ) :
    ∑ i ∈ range n, thgU n T H G i (i + s) = ∑ i ∈ range (n - s), thgU n T H G i (i + s) := by
  have hz : ∑ i ∈ Ico (n - s) n, thgU n T H G i (i + s) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [thgU_symm]
    exact thgU_zero _ (by omega)
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le n s), hz, add_zero]

theorem sum_range_ite_parity {M s n : ℕ} (hM : n = s + M + 2) (c : ℝ) :
    ∑ i ∈ range M, (if 2 * i + s + 3 = n then c else 0) = if (M + 2) % 2 = 1 then c else 0 := by
  by_cases hp : (M + 2) % 2 = 1
  · rw [if_pos hp, Finset.sum_eq_single ((M - 1) / 2)]
    · rw [if_pos (by omega)]
    · intro b _ hb
      rw [if_neg (by omega)]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · rw [if_neg hp]
    exact Finset.sum_eq_zero (fun i _ => by rw [if_neg (by omega)])

/-- **Run recurrence** (Lemmas 1.1-1.2): run `s` minus run `s+2`. -/
theorem thg_run_rec {s : ℕ} (hs : s + 3 ≤ n) :
    2 * ∑ i ∈ range n, thgU n T H G i (i + s) =
      2 * ∑ i ∈ range n, thgU n T H G i (i + (s + 2)) + ((n - s : ℕ) : ℝ) * T s -
        ((n - s - 2 : ℕ) : ℝ) * T (s + 2) + 2 * H (s + 1) +
        (if (n - s) % 2 = 1 then G s - G (s + 2) else 0) := by
  rw [thg_run_short, thg_run_short]
  obtain ⟨M, hM⟩ : ∃ M, n - s = M + 2 := ⟨n - s - 2, by omega⟩
  have hM2 : n - (s + 2) = M := by omega
  have hM3 : n - s - 2 = M := by omega
  have hn : n = s + M + 2 := by omega
  have hterm : ∀ i ∈ range M, thgU n T H G (i + 1) (i + 1 + s) =
      thgU n T H G i (i + (s + 2)) + (T s - T (s + 2)) / 2 +
        (if 2 * i + s + 3 = n then (G s - G (s + 2)) / 2 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have d1 : Nat.dist (i + 1) (i + 1 + s) = s := by unfold Nat.dist; omega
    have d2 : Nat.dist i (i + (s + 2)) = s + 2 := by unfold Nat.dist; omega
    by_cases h : 2 * i + s + 3 = n
    · rw [thgU_anti (by omega) (by omega) (by omega), thgU_anti (by omega) (by omega) (by omega),
        if_pos h, d1, d2]
      ring
    · rw [thgU_off (by omega) (by omega) (by omega), thgU_off (by omega) (by omega) (by omega),
        if_neg h, d1, d2, show min (i + 1 + (i + 1 + s) + 1) (2 * n - 1 - (i + 1 + (i + 1 + s))) =
          min (i + (i + (s + 2)) + 1) (2 * n - 1 - (i + (i + (s + 2)))) by omega]
      ring
  have e0 : thgU n T H G 0 (0 + s) = (T s + H (s + 1)) / 2 := by
    rw [thgU_off (by omega) (by omega) (by omega), show Nat.dist 0 (0 + s) = s by unfold Nat.dist; omega,
      show min (0 + (0 + s) + 1) (2 * n - 1 - (0 + (0 + s))) = s + 1 by omega]
  have eM : thgU n T H G (M + 1) (M + 1 + s) = (T s + H (s + 1)) / 2 := by
    rw [thgU_off (by omega) (by omega) (by omega),
      show Nat.dist (M + 1) (M + 1 + s) = s by unfold Nat.dist; omega,
      show min (M + 1 + (M + 1 + s) + 1) (2 * n - 1 - (M + 1 + (M + 1 + s))) = s + 1 by omega]
  have hpar := sum_range_ite_parity hn ((G s - G (s + 2)) / 2)
  rw [hM3, hM2, hM, Finset.sum_range_succ', Finset.sum_range_succ, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, Finset.sum_add_distrib, e0, eM, hpar, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast
  split_ifs <;> ring

theorem thg_run_top (hn : 1 ≤ n) :
    ∑ i ∈ range n, thgU n T H G i (i + (n - 1)) = (T (n - 1) + G (n - 1)) / 2 := by
  rw [thg_run_short, show n - (n - 1) = 1 by omega, Finset.sum_range_one,
    thgU_anti (by omega) (by omega) (by omega),
    show Nat.dist 0 (0 + (n - 1)) = n - 1 by unfold Nat.dist; omega]

theorem thg_run_top2 (hn : 2 ≤ n) :
    ∑ i ∈ range n, thgU n T H G i (i + (n - 2)) = T (n - 2) + H (n - 1) := by
  rw [thg_run_short, show n - (n - 2) = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one,
    thgU_off (i := 0) (j := 0 + (n - 2)) (by omega) (by omega) (by omega),
    thgU_off (i := 1) (j := 1 + (n - 2)) (by omega) (by omega) (by omega),
    show Nat.dist 0 (0 + (n - 2)) = n - 2 by unfold Nat.dist; omega,
    show Nat.dist 1 (1 + (n - 2)) = n - 2 by unfold Nat.dist; omega,
    show min (0 + (0 + (n - 2)) + 1) (2 * n - 1 - (0 + (0 + (n - 2)))) = n - 1 by omega,
    show min (1 + (1 + (n - 2)) + 1) (2 * n - 1 - (1 + (1 + (n - 2)))) = n - 1 by omega]
  ring

theorem thg_run_high {s : ℕ} (hs : n ≤ s) : ∑ i ∈ range n, thgU n T H G i (i + s) = 0 :=
  Finset.sum_eq_zero (fun i _ => by rw [thgU_symm]; exact thgU_zero _ (by omega))

/-- Row split: Toeplitz part, Hankel part as a function of `r + j`, and the antidiagonal cell. -/
theorem thg_row_split {r : ℕ} (hr : r < n) :
    2 * ∑ j ∈ range n, thgU n T H G r j =
      ∑ j ∈ range n, T (Nat.dist r j) + ∑ j ∈ range n, thgHk n H (r + j) +
        G (Nat.dist r (n - 1 - r)) := by
  have e : ∀ j ∈ range n, 2 * thgU n T H G r j =
      T (Nat.dist r j) + thgHk n H (r + j) + (if r + j + 1 = n then G (Nat.dist r j) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold thgU thgHk
    rw [if_pos (And.intro hr hj)]
    split_ifs <;> ring
  have hG : ∑ j ∈ range n, (if r + j + 1 = n then G (Nat.dist r j) else 0) =
      G (Nat.dist r (n - 1 - r)) := by
    rw [Finset.sum_eq_single (n - 1 - r)]
    · rw [if_pos (by omega)]
    · intro b _ hb
      rw [if_neg (by omega)]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  rw [Finset.mul_sum, Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, hG]

/-- **Row shift** (Lemma 1.3): row `r+1` minus row `r`. -/
theorem thg_row_succ {r : ℕ} (hr : r + 1 < n) :
    2 * ∑ j ∈ range n, thgU n T H G (r + 1) j =
      2 * ∑ j ∈ range n, thgU n T H G r j + (T (r + 1) - H (r + 1)) -
        (T (n - 1 - r) - H (n - 1 - r)) +
        (G (Nat.dist (r + 1) (n - 1 - (r + 1))) - G (Nat.dist r (n - 1 - r))) := by
  rw [thg_row_split hr, thg_row_split (by omega)]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hT1 : ∑ j ∈ range (N + 1), T (Nat.dist (r + 1) j) =
      ∑ j ∈ range N, T (Nat.dist r j) + T (r + 1) := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      unfold Nat.dist
      omega
    · congr 1
      unfold Nat.dist
      omega
  have hT0 : ∑ j ∈ range (N + 1), T (Nat.dist r j) =
      ∑ j ∈ range N, T (Nat.dist r j) + T (N + 1 - 1 - r) := by
    rw [Finset.sum_range_succ]
    congr 2
    unfold Nat.dist
    omega
  have hH1 : ∑ j ∈ range (N + 1), thgHk (N + 1) H (r + 1 + j) =
      ∑ j ∈ range N, thgHk (N + 1) H (r + (j + 1)) + H (N + 1 - 1 - r) := by
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      omega
    · unfold thgHk
      rw [if_neg (by omega)]
      congr 1
      omega
  have hH0 : ∑ j ∈ range (N + 1), thgHk (N + 1) H (r + j) =
      ∑ j ∈ range N, thgHk (N + 1) H (r + (j + 1)) + H (r + 1) := by
    rw [Finset.sum_range_succ']
    congr 1
    unfold thgHk
    rw [if_neg (by omega)]
    congr 1
    omega
  rw [hT1, hT0, hH1, hH0]
  ring

/-- **Cells** (Lemma 1.4): `0 ≤ U ≤ 1` from the one-dimensional conditions. -/
theorem thg_cells
    (hTH : ∀ s u, s < u → u + 1 ≤ n → (u - s) % 2 = 1 → 0 ≤ T s + H u ∧ T s + H u ≤ 2)
    (hTG : ∀ s, s < n → (n - s) % 2 = 1 → 0 ≤ T s + G s ∧ T s + G s ≤ 2) (i j : ℕ) :
    0 ≤ thgU n T H G i j ∧ thgU n T H G i j ≤ 1 := by
  by_cases hij : i < n ∧ j < n
  · by_cases ha : i + j + 1 = n
    · rw [thgU_anti hij.1 hij.2 ha]
      obtain ⟨h1, h2⟩ := hTG (Nat.dist i j) (by unfold Nat.dist; omega)
        (by unfold Nat.dist; omega)
      constructor <;> linarith
    · rw [thgU_off hij.1 hij.2 ha]
      obtain ⟨h1, h2⟩ := hTH (Nat.dist i j) (min (i + j + 1) (2 * n - 1 - (i + j)))
        (by unfold Nat.dist; omega) (by omega) (by unfold Nat.dist; omega)
      constructor <;> linarith
  · unfold thgU
    rw [if_neg hij]
    norm_num

end Generic

/-! ## Total mass and constant rows -/

/-- Diagonal decomposition of a box sum: upper runs and strictly lower runs. -/
theorem sum_box_runs (f : ℕ → ℕ → ℝ) : ∀ n,
    ∑ i ∈ range n, ∑ j ∈ range n, f i j =
      ∑ s ∈ range n, ∑ i ∈ range (n - s), f i (i + s) +
        ∑ s ∈ range n, ∑ i ∈ range (n - s - 1), f (i + s + 1) i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : ∑ s ∈ range (n + 1), ∑ i ∈ range (n + 1 - s), f i (i + s) =
        ∑ s ∈ range n, ∑ i ∈ range (n - s), f i (i + s) + ∑ i ∈ range (n + 1), f i n := by
      rw [Finset.sum_range_succ, show n + 1 - n = 1 by omega, Finset.sum_range_one]
      have e : ∀ s ∈ range n, ∑ i ∈ range (n + 1 - s), f i (i + s) =
          ∑ i ∈ range (n - s), f i (i + s) + f (n - s) n := by
        intro s hs
        rw [Finset.mem_range] at hs
        rw [show n + 1 - s = n - s + 1 by omega, Finset.sum_range_succ,
          show n - s + s = n by omega]
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_succ' (fun i => f i n)]
      have hr : ∑ s ∈ range n, f (n - s) n = ∑ i ∈ range n, f (i + 1) n := by
        rw [← Finset.sum_range_reflect (fun i => f (i + 1) n) n]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        rw [Finset.mem_range] at hs
        rw [show n - 1 - s + 1 = n - s by omega]
      rw [hr, zero_add]
      ring
    have hB : ∑ s ∈ range (n + 1), ∑ i ∈ range (n + 1 - s - 1), f (i + s + 1) i =
        ∑ s ∈ range n, ∑ i ∈ range (n - s - 1), f (i + s + 1) i + ∑ j ∈ range n, f n j := by
      rw [Finset.sum_range_succ, show n + 1 - n - 1 = 0 by omega, Finset.sum_range_zero, add_zero]
      have e : ∀ s ∈ range n, ∑ i ∈ range (n + 1 - s - 1), f (i + s + 1) i =
          ∑ i ∈ range (n - s - 1), f (i + s + 1) i + f n (n - s - 1) := by
        intro s hs
        rw [Finset.mem_range] at hs
        rw [show n + 1 - s - 1 = n - s - 1 + 1 by omega, Finset.sum_range_succ,
          show n - s - 1 + s + 1 = n by omega]
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_range_reflect (fun j => f n j) n]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [Finset.mem_range] at hs
      rw [show n - 1 - s = n - s - 1 by omega]
    rw [hA, hB, Finset.sum_range_succ, Finset.sum_range_succ (fun j => f n j)]
    have hrow : ∀ i ∈ range n, ∑ j ∈ range (n + 1), f i j = ∑ j ∈ range n, f i j + f i n :=
      fun i _ => Finset.sum_range_succ _ _
    rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, ih, Finset.sum_range_succ (fun i => f i n)]
    ring

/-- `∑_{s < n} (r_s + r_{s+1}) = ∑_{a ∈ [lo, hi]} (2a+1)` for the run totals `r_s` of `[lo, hi]`. -/
theorem sum_run_totals {n lo hi : ℕ} (hhi : hi < n) :
    ∑ s ∈ range n, (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) +
      ∑ s ∈ range n, (((Icc lo hi).filter (fun a => s + 1 ≤ a)).card : ℝ) =
      ∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1) := by
  simp only [← Finset.sum_boole]
  rw [Finset.sum_comm, Finset.sum_comm (s := range n), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_Icc] at ha
  have h1 : ∑ s ∈ range n, (if s ≤ a then (1 : ℝ) else 0) = (a : ℝ) + 1 := by
    have := sum_range_indicator n (a + 1)
    rw [show min n (a + 1) = a + 1 by omega] at this
    push_cast at this
    rw [← this]
    exact Finset.sum_congr rfl (fun s _ => by
      by_cases h : s ≤ a
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)])
  have h2 : ∑ s ∈ range n, (if s + 1 ≤ a then (1 : ℝ) else 0) = (a : ℝ) := by
    have := sum_range_indicator n a
    rw [show min n a = a by omega] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun s _ => by
      by_cases h : s + 1 ≤ a
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)])
  rw [h1, h2]
  ring

/-- A constant row sum of a symmetric configuration with the run totals of `[lo, hi]` is
`∑_{a ∈ [lo, hi]} (2a+1) / n`. -/
theorem row_const_value {n lo hi : ℕ} {u : ℕ → ℕ → ℝ} (hsym : ∀ i j, u i j = u j i)
    (hz : ∀ i j, n ≤ i → u i j = 0)
    (hrun : ∀ s, ∑ i ∈ range n, u i (i + s) = (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ))
    (hhi : hi < n) {c : ℝ} (hrow : ∀ r < n, ∑ j ∈ range n, u r j = c) :
    c = (∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1)) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hshort : ∀ s, ∑ i ∈ range (n - s), u i (i + s) =
      (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) := by
    intro s
    rw [← hrun s, ← Finset.sum_range_add_sum_Ico _ (Nat.sub_le n s)]
    rw [Finset.sum_eq_zero (s := Ico (n - s) n) (fun i hi => by
      rw [Finset.mem_Ico] at hi; rw [hsym]; exact hz _ _ (by omega)), add_zero]
  have htot := sum_box_runs u n
  rw [Finset.sum_congr rfl (fun r hr => hrow r (Finset.mem_range.1 hr)), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at htot
  have hlow : ∀ s ∈ range n, ∑ i ∈ range (n - s - 1), u (i + s + 1) i =
      (((Icc lo hi).filter (fun a => s + 1 ≤ a)).card : ℝ) := by
    intro s _
    rw [← hshort (s + 1), show n - (s + 1) = n - s - 1 by omega]
    exact Finset.sum_congr rfl (fun i _ => by rw [hsym, show i + (s + 1) = i + s + 1 by omega])
  rw [Finset.sum_congr rfl (fun s _ => hshort s), Finset.sum_congr rfl hlow,
    sum_run_totals hhi] at htot
  rw [← htot]
  field_simp

/-! ## The dipole construction -/

/-- `2x(x-1) - 2L²` for `x ≥ L+1`, and `0` otherwise. -/
def qPart (L x : ℕ) : ℝ := if L + 1 ≤ x then 2 * (x : ℝ) * ((x : ℝ) - 1) - 2 * (L : ℝ) ^ 2 else 0

/-- The pair-sum right-hand side `Q(x)` (Lemma 2.1). -/
def dipQ (K M : ℕ) (α : ℝ) (x : ℕ) : ℝ :=
  qPart K x - qPart M x + (if K + 2 ≤ x ∧ x ≤ 2 * K + 2 then 2 * ((K : ℝ) + 1) * α else 0)

/-- `τ` in `x = n - s` coordinates: `τ(0) = 0`, `τ(x) + τ(x-1) = Q(x)/(x(x-1))`. -/
def dipTau (K M : ℕ) (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | x + 1 => dipQ K M α (x + 1) / (((x : ℝ) + 1) * x) - dipTau K M α x

theorem dipTau_pair (K M : ℕ) (α : ℝ) (x : ℕ) :
    dipTau K M α (x + 1) + dipTau K M α x = dipQ K M α (x + 1) / (((x : ℝ) + 1) * x) := by
  rw [dipTau]
  ring

theorem qPart_succ (L x : ℕ) : qPart L (x + 1) - qPart L x =
    (x : ℝ) * ((if L ≤ x then 2 else 0) + (if L + 1 ≤ x then 2 else 0)) := by
  unfold qPart
  push_cast
  by_cases h1 : L + 1 ≤ x
  · rw [if_pos (by omega), if_pos h1, if_pos (by omega), if_pos h1]
    ring
  · by_cases h2 : L = x
    · subst h2
      rw [if_pos (by omega), if_neg h1, if_pos le_rfl, if_neg h1]
      ring
    · rw [if_neg (by omega), if_neg h1, if_neg (by omega), if_neg h1]
      ring

/-- The `Q`-difference identity (proof of Lemma 2.1). -/
theorem dipQ_succ (K M : ℕ) (α : ℝ) (x : ℕ) : dipQ K M α (x + 1) - dipQ K M α x =
    (x : ℝ) * ((if K ≤ x then 2 else 0) + (if K + 1 ≤ x then 2 else 0) -
      (if M ≤ x then 2 else 0) - (if M + 1 ≤ x then 2 else 0) +
      (if x = K + 1 then 2 * α else 0) - (if x = 2 * K + 2 then α else 0)) := by
  have hK := qPart_succ K x
  have hM := qPart_succ M x
  have hw : (if K + 2 ≤ x + 1 ∧ x + 1 ≤ 2 * K + 2 then 2 * ((K : ℝ) + 1) * α else 0) -
      (if K + 2 ≤ x ∧ x ≤ 2 * K + 2 then 2 * ((K : ℝ) + 1) * α else 0) =
      (x : ℝ) * ((if x = K + 1 then 2 * α else 0) - (if x = 2 * K + 2 then α else 0)) := by
    by_cases h1 : x = K + 1
    · subst h1
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega)]
      push_cast
      ring
    · by_cases h2 : x = 2 * K + 2
      · subst h2
        rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos rfl]
        push_cast
        ring
      · rw [if_neg h1, if_neg h2]
        by_cases h3 : K + 2 ≤ x ∧ x ≤ 2 * K + 2
        · rw [if_pos (by omega), if_pos h3]
          ring
        · rw [if_neg (by omega), if_neg h3]
          ring
  unfold dipQ
  linear_combination hK - hM + hw

variable {n lo hi : ℕ} {α : ℝ}

/-- `T(s) = τ(n - s)`. -/
def dipT (n K M : ℕ) (α : ℝ) (s : ℕ) : ℝ := dipTau K M α (n - s)

/-- `H(u) = T(u) - α [u = hi]` (the dipole at level `hi`). -/
def dipH (n hi K M : ℕ) (α : ℝ) (u : ℕ) : ℝ := dipT n K M α u - if u = hi then α else 0

/-- `G(u) = α [u ≤ 2 hi - n - 1]` (antidiagonal cells). -/
def dipG (n hi : ℕ) (α : ℝ) (u : ℕ) : ℝ := if u + n + 1 ≤ 2 * hi then α else 0

/-- The dipole construction for `[lo, hi]` in the `n`-box with amplitude `α`. -/
def dipU (n lo hi : ℕ) (α : ℝ) : ℕ → ℕ → ℝ :=
  thgU n (dipT n (n - 1 - hi) (n - lo) α) (dipH n hi (n - 1 - hi) (n - lo) α) (dipG n hi α)

/-- One step of the run recursion for the dipole construction. -/
theorem dip_run_step (hlohi : lo ≤ hi) (hhi : hi + 2 ≤ n) {s : ℕ}
    (hs : s + 3 ≤ n) :
    ∑ i ∈ range n, dipU n lo hi α i (i + s) =
      ∑ i ∈ range n, dipU n lo hi α i (i + (s + 2)) +
        ((((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) -
          (((Icc lo hi).filter (fun a => s + 2 ≤ a)).card : ℝ)) := by
  unfold dipU
  have hrec := thg_run_rec (T := dipT n (n - 1 - hi) (n - lo) α)
    (H := dipH n hi (n - 1 - hi) (n - lo) α) (G := dipG n hi α) hs
  obtain ⟨y, hy⟩ : ∃ y, n - s = y + 2 := ⟨n - s - 2, by omega⟩
  set K := n - 1 - hi with hK
  set M := n - lo with hM
  have hp2 := dipTau_pair K M α (y + 1)
  have hp1 := dipTau_pair K M α y
  have hq := dipQ_succ K M α (y + 1)
  have hTs : dipT n K M α s = dipTau K M α (y + 1 + 1) := by
    unfold dipT
    rw [hy]
  have hTs2 : dipT n K M α (s + 2) = dipTau K M α y := by
    unfold dipT
    rw [show n - (s + 2) = y by omega]
  have hHs : dipH n hi K M α (s + 1) = dipTau K M α (y + 1) - if y = K then α else 0 := by
    unfold dipH dipT
    rw [show n - (s + 1) = y + 1 by omega]
    congr 1
    by_cases h : y = K
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hG : (if (n - s) % 2 = 1 then dipG n hi α s - dipG n hi α (s + 2) else 0) =
      if y + 1 = 2 * K + 2 then α else 0 := by
    unfold dipG
    by_cases h1 : y + 1 = 2 * K + 2
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega), if_neg (by omega)]
      ring
    · rw [if_neg h1]
      by_cases h2 : (n - s) % 2 = 1
      · rw [if_pos h2]
        by_cases h3 : s + 2 + n + 1 ≤ 2 * hi
        · rw [if_pos h3, if_pos (by omega)]
          ring
        · rw [if_neg h3, if_neg (by omega)]
          ring
      · rw [if_neg h2]
  have hcard : ((((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) -
      (((Icc lo hi).filter (fun a => s + 2 ≤ a)).card : ℝ)) * 2 =
      (if K ≤ y + 1 then 2 else 0) + (if K + 1 ≤ y + 1 then 2 else 0) -
        (if M ≤ y + 1 then 2 else 0) - (if M + 1 ≤ y + 1 then 2 else 0) := by
    rw [card_filter_Icc_le, card_filter_Icc_le]
    have hnat : (hi + 1 - max lo s) + (if M ≤ y + 1 then 1 else 0) +
        (if M + 1 ≤ y + 1 then 1 else 0) =
        (hi + 1 - max lo (s + 2)) + (if K ≤ y + 1 then 1 else 0) +
        (if K + 1 ≤ y + 1 then 1 else 0) := by
      split_ifs <;> omega
    have hnat' := congrArg (fun m : ℕ => (m : ℝ)) hnat
    simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hnat'
    have e1 : ∀ c : Prop, [Decidable c] → ((if c then (2 : ℝ) else 0) = 2 * (if c then 1 else 0)) := by
      intro c _
      split_ifs <;> ring
    rw [e1 (K ≤ y + 1), e1 (K + 1 ≤ y + 1), e1 (M ≤ y + 1), e1 (M + 1 ≤ y + 1)]
    linarith
  rw [hTs, hTs2, hHs, hG, hy, show y + 2 - 2 = y by omega,
    show ((y + 2 : ℕ) : ℝ) = (y : ℝ) + 2 by push_cast; ring] at hrec
  rw [Nat.cast_succ] at hq hp2
  have hY1 : (y : ℝ) + 1 ≠ 0 := by positivity
  have hY0 : (y : ℝ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
  have hY2 : (y : ℝ) + 1 + 1 ≠ 0 := by positivity
  have e2 : ((y : ℝ) + 2) * (dipTau K M α (y + 1 + 1) + dipTau K M α (y + 1)) =
      dipQ K M α (y + 1 + 1) / ((y : ℝ) + 1) := by
    rw [hp2]
    field_simp
    ring
  have e1 : (y : ℝ) * (dipTau K M α (y + 1) + dipTau K M α y) =
      dipQ K M α (y + 1) / ((y : ℝ) + 1) := by
    rw [hp1]
    field_simp
  have e3 := congrArg (fun z : ℝ => z / ((y : ℝ) + 1)) hq
  rw [mul_div_cancel_left₀ _ hY1, sub_div] at e3
  have hyK : (if y + 1 = K + 1 then 2 * α else 0) = 2 * (if y = K then α else 0) := by
    by_cases h : y = K
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
      ring
  linarith

theorem dip_run (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi + 2 ≤ n) (s : ℕ) :
    ∑ i ∈ range n, dipU n lo hi α i (i + s) =
      (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) := by
  have hcard0 : ∀ s, hi < s → (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) = 0 := by
    intro s hs
    rw [card_filter_Icc_le, show hi + 1 - max lo s = 0 by omega]
    simp
  have main : ∀ q s, n ≤ s + q + 2 → ∑ i ∈ range n, dipU n lo hi α i (i + s) =
      (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) := by
    intro q
    induction q with
    | zero =>
      intro s hs
      by_cases h1 : n ≤ s
      · unfold dipU
        rw [thg_run_high h1, hcard0 s (by omega)]
      · by_cases h2 : s = n - 1
        · subst h2
          unfold dipU
          rw [thg_run_top (by omega), hcard0 (n - 1) (by omega)]
          unfold dipT dipG
          rw [show n - (n - 1) = 1 by omega, if_neg (by omega)]
          simp [dipTau]
        · have h3 : s = n - 2 := by omega
          subst h3
          unfold dipU
          rw [thg_run_top2 (by omega)]
          unfold dipH dipT
          rw [show n - (n - 2) = 1 + 1 by omega, show n - (n - 1) = 1 by omega,
            if_neg (by omega), sub_zero]
          have hp := dipTau_pair (n - 1 - hi) (n - lo) α 1
          have h0 : dipTau (n - 1 - hi) (n - lo) α 1 = 0 := by simp [dipTau]
          rw [card_filter_Icc_le]
          by_cases hK : hi = n - 2
          · have hQ : dipQ (n - 1 - hi) (n - lo) α (1 + 1) = 2 := by
              unfold dipQ qPart
              rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
              rw [show n - 1 - hi = 1 by omega]
              norm_num
            rw [hQ] at hp
            rw [show hi + 1 - max lo (n - 2) = 1 by omega]
            norm_num at hp ⊢
            linarith
          · have hQ : dipQ (n - 1 - hi) (n - lo) α (1 + 1) = 0 := by
              unfold dipQ qPart
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
              ring
            rw [hQ] at hp
            rw [show hi + 1 - max lo (n - 2) = 0 by omega]
            norm_num at hp ⊢
            linarith
    | succ q ih =>
      intro s hs
      by_cases h : n ≤ s + q + 2
      · exact ih s h
      · rw [dip_run_step hlohi hhi (show s + 3 ≤ n by omega), ih (s + 2) (by omega)]
        ring
  exact main n s (by omega)

/-- The dipole identity: consecutive rows agree (needs `α = 0` or `2 hi ≥ n`). -/
theorem dip_row_succ (hhi : hi + 2 ≤ n) (hα : α = 0 ∨ n ≤ 2 * hi) {r : ℕ} (hr : r + 1 < n) :
    ∑ j ∈ range n, dipU n lo hi α (r + 1) j = ∑ j ∈ range n, dipU n lo hi α r j := by
  have h := thg_row_succ (T := dipT n (n - 1 - hi) (n - lo) α)
    (H := dipH n hi (n - 1 - hi) (n - lo) α) (G := dipG n hi α) hr
  have e1 : dipT n (n - 1 - hi) (n - lo) α (r + 1) - dipH n hi (n - 1 - hi) (n - lo) α (r + 1) =
      if r + 1 = hi then α else 0 := by
    unfold dipH
    ring
  have e2 : dipT n (n - 1 - hi) (n - lo) α (n - 1 - r) -
      dipH n hi (n - 1 - hi) (n - lo) α (n - 1 - r) = if n - 1 - r = hi then α else 0 := by
    unfold dipH
    ring
  rw [e1, e2] at h
  have hz : (if r + 1 = hi then α else 0) - (if n - 1 - r = hi then α else 0) +
      (dipG n hi α (Nat.dist (r + 1) (n - 1 - (r + 1))) - dipG n hi α (Nat.dist r (n - 1 - r))) =
      0 := by
    unfold dipG
    rcases hα with h0 | h0
    · subst h0
      simp
    · unfold Nat.dist
      split_ifs <;> first | (exfalso; omega) | ring
  unfold dipU
  linarith

/-- **The dipole construction is an interval uniformisation of `[lo, hi]`** given the
one-dimensional cell conditions on `τ` (`η(y) = τ(y) - α[y = K+1]`, `γ(x) = α[x ≥ 2K+3]`). -/
theorem isIntervalUnif_dip (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi + 2 ≤ n)
    (hα : α = 0 ∨ n ≤ 2 * hi)
    (hc1 : ∀ x y, 1 ≤ y → y < x → x ≤ n → (x - y) % 2 = 1 →
      0 ≤ dipTau (n - 1 - hi) (n - lo) α x +
          (dipTau (n - 1 - hi) (n - lo) α y - if y = n - 1 - hi + 1 then α else 0) ∧
        dipTau (n - 1 - hi) (n - lo) α x +
          (dipTau (n - 1 - hi) (n - lo) α y - if y = n - 1 - hi + 1 then α else 0) ≤ 2)
    (hc2 : ∀ x, 1 ≤ x → x ≤ n → x % 2 = 1 →
      0 ≤ dipTau (n - 1 - hi) (n - lo) α x + (if 2 * (n - 1 - hi) + 3 ≤ x then α else 0) ∧
        dipTau (n - 1 - hi) (n - lo) α x + (if 2 * (n - 1 - hi) + 3 ≤ x then α else 0) ≤ 2) :
    IsIntervalUnif n lo hi (dipU n lo hi α) := by
  have hcells : ∀ i j, 0 ≤ dipU n lo hi α i j ∧ dipU n lo hi α i j ≤ 1 := by
    intro i j
    unfold dipU
    refine thg_cells (fun s u hsu hu hodd => ?_) (fun s hs hodd => ?_) i j
    · have h := hc1 (n - s) (n - u) (by omega) (by omega) (by omega) (by omega)
      unfold dipH dipT
      rw [show (if u = hi then α else 0) = (if n - u = n - 1 - hi + 1 then α else 0) by
        by_cases hh : u = hi
        · rw [if_pos hh, if_pos (by omega)]
        · rw [if_neg hh, if_neg (by omega)]]
      exact h
    · have h := hc2 (n - s) (by omega) (by omega) (by omega)
      unfold dipT dipG
      rw [show (if s + n + 1 ≤ 2 * hi then α else 0) =
          (if 2 * (n - 1 - hi) + 3 ≤ n - s then α else 0) by
        by_cases hh : s + n + 1 ≤ 2 * hi
        · rw [if_pos hh, if_pos (by omega)]
        · rw [if_neg hh, if_neg (by omega)]]
      exact h
  have hsym : ∀ i j, dipU n lo hi α i j = dipU n lo hi α j i := fun i j => thgU_symm i j
  have hz : ∀ i j, n ≤ i → dipU n lo hi α i j = 0 := fun i j hi' => thgU_zero j hi'
  have hrun := dip_run (α := α) hlo hlohi hhi
  have hrowc : ∀ r < n, ∑ j ∈ range n, dipU n lo hi α r j =
      ∑ j ∈ range n, dipU n lo hi α 0 j := by
    intro r
    induction r with
    | zero => intro _; rfl
    | succ r ih =>
      intro hr
      rw [dip_row_succ hhi hα hr, ih (by omega)]
  have hval := row_const_value hsym hz hrun (by omega) hrowc
  exact
    { symm := hsym
      nonneg := fun i j => (hcells i j).1
      le_one := fun i j => (hcells i j).2
      zero := hz
      run := hrun
      row := fun r hr => by rw [hrowc r hr, hval] }

end STUProof
