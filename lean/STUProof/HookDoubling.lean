import STUProof.HookCertificates

/-!
# The doubling lemma for hook decompositions

A hook decomposition of the `M`-box gives one of the `2M`-box (P-HOOK,
`iqoqi/programs/hook/LOG.md`). Split the `2M`-box into `A = [0, M)` and `B = [M, 2M)` and let
`Y_c` (`c < M`) be the symmetric cell form of the given hooks. Then
* the new hook `c < M` is `Y_c / 2` on `A × A` and (shifted) on `B × B`;
* the new hook `M + c` is `Y_{M-1-c} / 2` on `A × A` and on `B × B`, plus `Y_c` on the cross
  block `A × B` (the cell `(i, M + j)` gets `Y_c(i, j)`) and on its mirror image `B × A`.

The cross cell `(i, M + j)` lies on the run `M + (j - i)`, so the cross part of the hook `M + c`
gives one unit to each run `M - c, …, M + c`, and its diagonal blocks give one unit to each run
`0, …, M - 1 - c`. Rows: `(2M - 2c - 1)/(2M) + (2c + 1)/M = (2(M + c) + 1)/(2M)`. Cells: the
diagonal blocks are covered by `J/2 + J/2`, the cross blocks by `∑_c Y_c = J`.

The proof uses the symmetric *cell form* `IsHookCells` of a hook decomposition, which is
equivalent to the run form `IsHookDecomposition` (`isHookCells_hookCell`,
`IsHookCells.isHookDecomposition`).

## Main results

* `hookDecomposition_double : HookDecomposition M → HookDecomposition (2 * M)`;
* `hookDecomposition_two_pow_mul : HookDecomposition m → ∀ k, HookDecomposition (2 ^ k * m)`;
* `hookDecomposition_pow2 : ∀ k, HookDecomposition (2 ^ k)`.
-/

open Finset

noncomputable section

namespace STUProof

/-! ## The cell form of a hook decomposition -/

/-- Cell form of a hook decomposition of the `n`-box: symmetric configurations `W a` that vanish
off the box and are nonnegative for `a < n`, such that for every hook `a < n` the run `s` has
total `[s ≤ a]` and every row has total `(2a+1)/n`, and the hooks `a < n` cover every cell of the
box exactly once. -/
structure IsHookCells (n : ℕ) (W : ℕ → ℕ → ℕ → ℝ) : Prop where
  symm : ∀ a i j, W a i j = W a j i
  zero : ∀ a i j, n ≤ i → W a i j = 0
  nonneg : ∀ a < n, ∀ i j, 0 ≤ W a i j
  run : ∀ a < n, ∀ s, ∑ i ∈ range n, W a i (i + s) = if s ≤ a then 1 else 0
  row : ∀ a < n, ∀ r < n, ∑ j ∈ range n, W a r j = (2 * (a : ℝ) + 1) / n
  cell : ∀ i < n, ∀ j < n, ∑ a ∈ range n, W a i j = 1

variable {n : ℕ} {W : ℕ → ℕ → ℕ → ℝ}

namespace IsHookCells

theorem zero' (h : IsHookCells n W) (a i j : ℕ) (hj : n ≤ j) : W a i j = 0 := by
  rw [h.symm]
  exact h.zero a j i hj

/-- The entries of hook `a` beyond its band vanish. -/
theorem band (h : IsHookCells n W) {a : ℕ} (ha : a < n) (i : ℕ) {s : ℕ} (hs : a < s) :
    W a i (i + s) = 0 := by
  by_cases hi : i < n
  · have h0 : ∑ k ∈ range n, W a k (k + s) = 0 := by
      rw [h.run a ha s, if_neg (by omega)]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h.nonneg a ha k (k + s))).1 h0 i
      (Finset.mem_range.2 hi)
  · exact h.zero a i (i + s) (by omega)

/-- Lower runs: `∑_{i ≥ t} W a i (i - t) = [t ≤ a]`. -/
theorem run_lower (h : IsHookCells n W) {a : ℕ} (ha : a < n) (t : ℕ) :
    ∑ i ∈ range n, (if t ≤ i then W a i (i - t) else 0) = if t ≤ a then 1 else 0 := by
  by_cases htn : t ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = t + m := ⟨n - t, by omega⟩
    have hsplit : ∑ i ∈ range (t + m), (if t ≤ i then W a i (i - t) else 0) =
        ∑ i ∈ range t, (if t ≤ i then W a i (i - t) else 0) +
          ∑ k ∈ range m, (if t ≤ t + k then W a (t + k) (t + k - t) else 0) :=
      Finset.sum_range_add (fun i => if t ≤ i then W a i (i - t) else 0) t m
    have h1 : ∑ i ∈ range t, (if t ≤ i then W a i (i - t) else 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_range] at hi; omega))
    have h2 : ∑ k ∈ range m, (if t ≤ t + k then W a (t + k) (t + k - t) else 0) =
        ∑ k ∈ range m, W a k (k + t) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [if_pos (Nat.le_add_right t k), Nat.add_sub_cancel_left, h.symm a (t + k) k,
        Nat.add_comm t k]
    have h3 : ∑ k ∈ range (t + m), W a k (k + t) = ∑ k ∈ range m, W a k (k + t) := by
      have hz : ∑ k ∈ Ico m (t + m), W a k (k + t) = 0 := by
        refine Finset.sum_eq_zero (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        exact h.zero' a k (k + t) (by omega)
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left m t), hz, add_zero]
    rw [hsplit, h1, zero_add, h2, ← h3, h.run a ha t]
  · rw [Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_range] at hi; omega)),
      if_neg (by omega)]

/-- A cell-form hook decomposition gives a run-form one (`x a s i = W a i (i + s)`). -/
theorem isHookDecomposition (h : IsHookCells n W) :
    IsHookDecomposition n (fun a s i => W a i (i + s)) := by
  refine ⟨fun a ha s _ i _ => h.nonneg a ha i (i + s), ?_, ?_, ?_⟩
  · intro a ha s hs
    show ∑ i ∈ range (n - s), W a i (i + s) = 1
    have hz : ∑ i ∈ Ico (n - s) n, W a i (i + s) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Finset.mem_Ico] at hi
      exact h.zero' a i (i + s) (by omega)
    have hrun := h.run a ha s
    rw [if_pos hs, ← Finset.sum_range_add_sum_Ico _ (Nat.sub_le n s), hz, add_zero] at hrun
    exact hrun
  · intro a ha r hr
    show W a r (r + 0) + ∑ s ∈ Icc 1 a, ((if r + s ≤ n - 1 then W a r (r + s) else 0) +
      (if s ≤ r then W a (r - s) (r - s + s) else 0)) = (2 * (a : ℝ) + 1) / n
    rw [← h.row a ha r hr, sum_range_split_row _ hr, Nat.add_zero]
    congr 1
    have hIcc : ∀ m, Icc 1 m = Ioc 0 m := fun m => by ext s; simp; omega
    rw [hIcc, hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) (by omega : a ≤ n - 1)]
    have hrest : ∑ s ∈ Ioc a (n - 1), ((if r + s < n then W a r (r + s) else 0) +
        (if s ≤ r then W a r (r - s) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun s hs => ?_)
      rw [Finset.mem_Ioc] at hs
      have e1 : W a r (r + s) = 0 := h.band ha r (by omega)
      by_cases hsr : s ≤ r
      · have e2 : W a r (r - s) = 0 := by
          rw [h.symm]
          have e3 := h.band ha (r - s) (show a < s by omega)
          rwa [Nat.sub_add_cancel hsr] at e3
        simp [e1, e2]
      · simp [e1, hsr]
    rw [hrest, add_zero]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Finset.mem_Ioc] at hs
    congr 1
    · by_cases h1 : r + s < n
      · rw [if_pos (by omega), if_pos h1]
      · rw [if_neg (by omega), if_neg h1]
    · by_cases h2 : s ≤ r
      · rw [if_pos h2, if_pos h2, Nat.sub_add_cancel h2, h.symm a (r - s) r]
      · rw [if_neg h2, if_neg h2]
  · intro s hs i hi
    show ∑ a ∈ Ico s n, W a i (i + s) = 1
    have hz : ∑ a ∈ range s, W a i (i + s) = 0 := by
      refine Finset.sum_eq_zero (fun a ha => ?_)
      rw [Finset.mem_range] at ha
      exact h.band (by omega) i ha
    have hcell := h.cell i (by omega) (i + s) (by omega)
    rw [← Finset.sum_range_add_sum_Ico _ hs.le, hz, zero_add] at hcell
    exact hcell

end IsHookCells

/-- The symmetric cell form `hookCell` of a run-form hook decomposition is a cell-form hook
decomposition. -/
theorem isHookCells_hookCell {x : ℕ → ℕ → ℕ → ℝ} (hx : IsHookDecomposition n x) :
    IsHookCells n (hookCell n x) :=
  { symm := hookCell_symm n x
    zero := fun a i j hi => by
      simp only [hookCell]
      rw [if_neg (by omega)]
    nonneg := fun a ha i j => hookCell_nonneg hx ha i j
    run := fun a ha s => hookCell_run hx ha s n (Nat.sub_le n s)
    row := fun a ha r hr => hookCell_row hx ha hr n le_rfl
    cell := fun i hi j hj => hookCell_cells hx hi hj }

/-- `HookDecomposition n` holds iff there is a cell-form hook decomposition of the `n`-box. -/
theorem hookDecomposition_iff_cells : HookDecomposition n ↔ ∃ W, IsHookCells n W :=
  ⟨fun ⟨_, hx⟩ => ⟨_, isHookCells_hookCell hx⟩, fun ⟨_, h⟩ => ⟨_, h.isHookDecomposition⟩⟩

/-! ## The doubling construction -/

/-- Block form on the `2M`-box (`A = [0, M)`, `B = [M, 2M)`): `D / 2` on `A × A` and (shifted)
on `B × B`, and `C` on the cross block `A × B` (the cell `(i, M + j)` gets `C i j`) and on its
mirror image `B × A`. -/
def dblCell (M : ℕ) (D C : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i < M then (if j < M then D i j / 2 else C i (j - M))
  else (if j < M then C j (i - M) else D (i - M) (j - M) / 2)

section dblCell

variable {M : ℕ} {D C : ℕ → ℕ → ℝ}

theorem dblCell_AA {i j : ℕ} (hi : i < M) (hj : j < M) : dblCell M D C i j = D i j / 2 := by
  unfold dblCell
  rw [if_pos hi, if_pos hj]

theorem dblCell_AB {i j : ℕ} (hi : i < M) (hj : M ≤ j) : dblCell M D C i j = C i (j - M) := by
  unfold dblCell
  rw [if_pos hi, if_neg (not_lt.2 hj)]

theorem dblCell_BA {i j : ℕ} (hi : M ≤ i) (hj : j < M) : dblCell M D C i j = C j (i - M) := by
  unfold dblCell
  rw [if_neg (not_lt.2 hi), if_pos hj]

theorem dblCell_BB {i j : ℕ} (hi : M ≤ i) (hj : M ≤ j) :
    dblCell M D C i j = D (i - M) (j - M) / 2 := by
  unfold dblCell
  rw [if_neg (not_lt.2 hi), if_neg (not_lt.2 hj)]

theorem dblCell_symm (hD : ∀ i j, D i j = D j i) (i j : ℕ) :
    dblCell M D C i j = dblCell M D C j i := by
  rcases lt_or_ge i M with hi | hi <;> rcases lt_or_ge j M with hj | hj
  · rw [dblCell_AA hi hj, dblCell_AA hj hi, hD i j]
  · rw [dblCell_AB hi hj, dblCell_BA hj hi]
  · rw [dblCell_BA hi hj, dblCell_AB hj hi]
  · rw [dblCell_BB hi hj, dblCell_BB hj hi, hD (i - M) (j - M)]

theorem dblCell_nonneg (hD : ∀ i j, 0 ≤ D i j) (hC : ∀ i j, 0 ≤ C i j) (i j : ℕ) :
    0 ≤ dblCell M D C i j := by
  rcases lt_or_ge i M with hi | hi <;> rcases lt_or_ge j M with hj | hj
  · rw [dblCell_AA hi hj]
    exact div_nonneg (hD i j) (by norm_num)
  · rw [dblCell_AB hi hj]
    exact hC _ _
  · rw [dblCell_BA hi hj]
    exact hC _ _
  · rw [dblCell_BB hi hj]
    exact div_nonneg (hD _ _) (by norm_num)

theorem dblCell_zero (hD : ∀ i j, M ≤ i → D i j = 0) (hC : ∀ i j, M ≤ j → C i j = 0)
    {i : ℕ} (j : ℕ) (hi : 2 * M ≤ i) : dblCell M D C i j = 0 := by
  rcases lt_or_ge j M with hj | hj
  · rw [dblCell_BA (by omega) hj, hC j (i - M) (by omega)]
  · rw [dblCell_BB (by omega) hj, hD (i - M) (j - M) (by omega), zero_div]

/-- Rows of the block form through `A`. -/
theorem dblCell_row_A {r : ℕ} (hr : r < M) :
    ∑ j ∈ range (2 * M), dblCell M D C r j =
      (∑ j ∈ range M, D r j) / 2 + ∑ j ∈ range M, C r j := by
  have hsplit : ∑ j ∈ range (2 * M), dblCell M D C r j =
      ∑ j ∈ range M, dblCell M D C r j + ∑ j ∈ range M, dblCell M D C r (M + j) := by
    rw [two_mul, Finset.sum_range_add]
  rw [hsplit, Finset.sum_div]
  congr 1
  · exact Finset.sum_congr rfl (fun j hj => dblCell_AA hr (Finset.mem_range.1 hj))
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [dblCell_AB hr (Nat.le_add_right M j), Nat.add_sub_cancel_left]

/-- Rows of the block form through `B`. -/
theorem dblCell_row_B (r : ℕ) :
    ∑ j ∈ range (2 * M), dblCell M D C (M + r) j =
      ∑ j ∈ range M, C j r + (∑ j ∈ range M, D r j) / 2 := by
  have hsplit : ∑ j ∈ range (2 * M), dblCell M D C (M + r) j =
      ∑ j ∈ range M, dblCell M D C (M + r) j +
        ∑ j ∈ range M, dblCell M D C (M + r) (M + j) := by
    rw [two_mul, Finset.sum_range_add]
  rw [hsplit, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [dblCell_BA (Nat.le_add_right M r) (Finset.mem_range.1 hj), Nat.add_sub_cancel_left]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [dblCell_BB (Nat.le_add_right M r) (Nat.le_add_right M j),
      show M + r - M = r by omega, show M + j - M = j by omega]

/-- Runs of the block form: both diagonal blocks together give the run of `D`, the cross block
gives the shifted runs of `C`. -/
theorem dblCell_run (hD : ∀ i j, M ≤ j → D i j = 0) (s : ℕ) :
    ∑ i ∈ range (2 * M), dblCell M D C i (i + s) =
      ∑ i ∈ range M, D i (i + s) +
        ∑ i ∈ range M, (if M ≤ i + s then C i (i + s - M) else 0) := by
  have hsplit : ∑ i ∈ range (2 * M), dblCell M D C i (i + s) =
      ∑ i ∈ range M, dblCell M D C i (i + s) +
        ∑ i ∈ range M, dblCell M D C (M + i) (M + i + s) := by
    rw [two_mul, Finset.sum_range_add]
  have h1 : ∀ i ∈ range M, dblCell M D C i (i + s) =
      D i (i + s) / 2 + (if M ≤ i + s then C i (i + s - M) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases his : i + s < M
    · rw [dblCell_AA hi his, if_neg (by omega), add_zero]
    · rw [dblCell_AB hi (by omega), if_pos (by omega), hD i (i + s) (by omega), zero_div,
        zero_add]
  have h2 : ∀ i ∈ range M, dblCell M D C (M + i) (M + i + s) = D i (i + s) / 2 := by
    intro i _
    rw [dblCell_BB (by omega) (by omega), show M + i - M = i by omega,
      show M + i + s - M = i + s by omega]
  have hhalf : ∑ i ∈ range M, D i (i + s) / 2 = (∑ i ∈ range M, D i (i + s)) / 2 := by
    rw [Finset.sum_div]
  rw [hsplit, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, hhalf]
  ring

end dblCell

/-- The doubled family on the `2M`-box: the hook `a < M` is `dblCell M (W a) 0`, the hook
`a = M + c` is `dblCell M (W (M - 1 - c)) (W c)`. -/
def dblW (M : ℕ) (W : ℕ → ℕ → ℕ → ℝ) (a : ℕ) : ℕ → ℕ → ℝ :=
  if a < M then dblCell M (W a) (fun _ _ => 0) else dblCell M (W (2 * M - 1 - a)) (W (a - M))

theorem dblW_lo {M a : ℕ} (ha : a < M) : dblW M W a = dblCell M (W a) (fun _ _ => 0) := by
  unfold dblW
  rw [if_pos ha]

theorem dblW_ge {M a : ℕ} (ha : M ≤ a) :
    dblW M W a = dblCell M (W (2 * M - 1 - a)) (W (a - M)) := by
  unfold dblW
  rw [if_neg (not_lt.2 ha)]

theorem dblW_hi {M c : ℕ} (hc : c < M) :
    dblW M W (M + c) = dblCell M (W (M - 1 - c)) (W c) := by
  rw [dblW_ge (Nat.le_add_right M c), show 2 * M - 1 - (M + c) = M - 1 - c by omega,
    show M + c - M = c by omega]

namespace IsHookCells

/-- Cross runs: the cross part of the new hook `M + c` has run totals `[M - c ≤ s ≤ M + c]`. -/
theorem run_cross {M : ℕ} (h : IsHookCells M W) {c : ℕ} (hc : c < M) (s : ℕ) :
    ∑ i ∈ range M, (if M ≤ i + s then W c i (i + s - M) else 0) =
      if s ≤ M + c ∧ M ≤ s + c then 1 else 0 := by
  by_cases hs : M ≤ s
  · have e : ∀ i ∈ range M, (if M ≤ i + s then W c i (i + s - M) else 0) =
        W c i (i + (s - M)) := by
      intro i _
      rw [if_pos (by omega), show i + s - M = i + (s - M) by omega]
    rw [Finset.sum_congr rfl e, h.run c hc (s - M)]
    by_cases ht : s - M ≤ c
    · rw [if_pos ht, if_pos (by omega)]
    · rw [if_neg ht, if_neg (by omega)]
  · have e : ∀ i ∈ range M, (if M ≤ i + s then W c i (i + s - M) else 0) =
        (if M - s ≤ i then W c i (i - (M - s)) else 0) := by
      intro i _
      by_cases hi : M ≤ i + s
      · rw [if_pos hi, if_pos (by omega), show i + s - M = i - (M - s) by omega]
      · rw [if_neg hi, if_neg (by omega)]
    rw [Finset.sum_congr rfl e, h.run_lower hc (M - s)]
    by_cases ht : M - s ≤ c
    · rw [if_pos ht, if_pos (by omega)]
    · rw [if_neg ht, if_neg (by omega)]

/-- **Doubling lemma** (cell form): a hook decomposition of the `M`-box gives one of the
`2M`-box. -/
theorem double {M : ℕ} (h : IsHookCells M W) : IsHookCells (2 * M) (dblW M W) :=
  { symm := by
      intro a i j
      rcases lt_or_ge a M with h1 | h1
      · rw [dblW_lo h1]
        exact dblCell_symm (h.symm a) i j
      · rw [dblW_ge h1]
        exact dblCell_symm (h.symm _) i j
    zero := by
      intro a i j hi
      rcases lt_or_ge a M with h1 | h1
      · rw [dblW_lo h1]
        exact dblCell_zero (h.zero a) (fun _ _ _ => rfl) j hi
      · rw [dblW_ge h1]
        exact dblCell_zero (h.zero _) (h.zero' _) j hi
    nonneg := by
      intro a ha i j
      rcases lt_or_ge a M with h1 | h1
      · rw [dblW_lo h1]
        exact dblCell_nonneg (h.nonneg a h1) (fun _ _ => le_rfl) i j
      · obtain ⟨c, rfl⟩ : ∃ c, a = M + c := ⟨a - M, by omega⟩
        rw [dblW_hi (show c < M by omega)]
        exact dblCell_nonneg (h.nonneg (M - 1 - c) (by omega)) (h.nonneg c (by omega)) i j
    run := by
      intro a ha s
      rcases lt_or_ge a M with h1 | h1
      · rw [dblW_lo h1, dblCell_run (h.zero' a) s, h.run a h1 s]
        simp only [ite_self, Finset.sum_const_zero, add_zero]
      · obtain ⟨c, rfl⟩ : ∃ c, a = M + c := ⟨a - M, by omega⟩
        have hc : c < M := by omega
        rw [dblW_hi hc, dblCell_run (h.zero' (M - 1 - c)) s, h.run (M - 1 - c) (by omega) s,
          h.run_cross hc s]
        split_ifs <;> first | (exfalso; omega) | norm_num
    row := by
      intro a ha r hr
      rcases lt_or_ge a M with h1 | h1
      · rw [dblW_lo h1]
        rcases lt_or_ge r M with h2 | h2
        · rw [dblCell_row_A h2, h.row a h1 r h2]
          simp only [Finset.sum_const_zero, add_zero]
          push_cast
          ring
        · obtain ⟨r', rfl⟩ : ∃ r', r = M + r' := ⟨r - M, by omega⟩
          rw [dblCell_row_B r', h.row a h1 r' (by omega)]
          simp only [Finset.sum_const_zero, zero_add]
          push_cast
          ring
      · obtain ⟨c, rfl⟩ : ∃ c, a = M + c := ⟨a - M, by omega⟩
        have hc : c < M := by omega
        have hb : ((M - 1 - c : ℕ) : ℝ) = (M : ℝ) - 1 - c := by
          have e : M - 1 - c + c + 1 = M := by omega
          have e' : ((M - 1 - c : ℕ) : ℝ) + c + 1 = M := by exact_mod_cast e
          linarith
        rw [dblW_hi hc]
        rcases lt_or_ge r M with h2 | h2
        · rw [dblCell_row_A h2, h.row (M - 1 - c) (by omega) r h2, h.row c hc r h2, hb]
          push_cast
          ring
        · obtain ⟨r', rfl⟩ : ∃ r', r = M + r' := ⟨r - M, by omega⟩
          have e : ∑ j ∈ range M, W c j r' = ∑ j ∈ range M, W c r' j :=
            Finset.sum_congr rfl (fun j _ => h.symm c j r')
          rw [dblCell_row_B r', e, h.row c hc r' (by omega),
            h.row (M - 1 - c) (by omega) r' (by omega), hb]
          push_cast
          ring
    cell := by
      intro i hi j hj
      have hsplit : ∑ a ∈ range (2 * M), dblW M W a i j =
          ∑ a ∈ range M, dblW M W a i j + ∑ c ∈ range M, dblW M W (M + c) i j := by
        rw [two_mul, Finset.sum_range_add]
      have e1 : ∀ a ∈ range M, dblW M W a i j = dblCell M (W a) (fun _ _ => 0) i j :=
        fun a ha => by rw [dblW_lo (Finset.mem_range.1 ha)]
      have e2 : ∀ c ∈ range M, dblW M W (M + c) i j = dblCell M (W (M - 1 - c)) (W c) i j :=
        fun c hc => by rw [dblW_hi (Finset.mem_range.1 hc)]
      rw [hsplit, Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
      rcases lt_or_ge i M with h1 | h1 <;> rcases lt_or_ge j M with h2 | h2
      · simp only [dblCell_AA h1 h2]
        have hr : ∑ c ∈ range M, W (M - 1 - c) i j / 2 = ∑ c ∈ range M, W c i j / 2 :=
          Finset.sum_range_reflect (fun c => W c i j / 2) M
        rw [hr, ← Finset.sum_div, h.cell i h1 j h2]
        norm_num
      · simp only [dblCell_AB h1 h2, Finset.sum_const_zero, zero_add]
        exact h.cell i h1 (j - M) (by omega)
      · simp only [dblCell_BA h1 h2, Finset.sum_const_zero, zero_add]
        exact h.cell j h2 (i - M) (by omega)
      · simp only [dblCell_BB h1 h2]
        have hr : ∑ c ∈ range M, W (M - 1 - c) (i - M) (j - M) / 2 =
            ∑ c ∈ range M, W c (i - M) (j - M) / 2 :=
          Finset.sum_range_reflect (fun c => W c (i - M) (j - M) / 2) M
        rw [hr, ← Finset.sum_div, h.cell (i - M) (by omega) (j - M) (by omega)]
        norm_num }

end IsHookCells

/-! ## Main results -/

/-- **Doubling lemma**: a hook decomposition of the `M`-box gives one of the `2M`-box. -/
theorem hookDecomposition_double {M : ℕ} (h : HookDecomposition M) :
    HookDecomposition (2 * M) := by
  obtain ⟨_, h⟩ := hookDecomposition_iff_cells.1 h
  exact hookDecomposition_iff_cells.2 ⟨_, h.double⟩

/-- Iterated doubling: `HookDecomposition m → HookDecomposition (2^k m)`. -/
theorem hookDecomposition_two_pow_mul {m : ℕ} (h : HookDecomposition m) :
    ∀ k, HookDecomposition (2 ^ k * m) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc]
    exact hookDecomposition_double ih

/-- **Hook Decomposition Lemma for all powers of two.** -/
theorem hookDecomposition_pow2 : ∀ k, HookDecomposition (2 ^ k) := by
  intro k
  simpa using hookDecomposition_two_pow_mul hookDecomposition_1 k

end STUProof
