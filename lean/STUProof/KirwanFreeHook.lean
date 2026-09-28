import STUProof.KirwanFreeCore

/-!
# Kirwan-free route, part 2: hook decompositions and uniformisation

A *hook decomposition* of the `n`-box (P-STU3, `stu3/exact_hookdec.py`) is a family of
configurations `x^(a)` (`a = 0, …, n-1`) in run coordinates, `x a s i` being the value on the
cell `(i, i+s)` of the upper run `s ≤ a` (and, by symmetry, on `(i+s, i)`), with
* (run) every run `s ≤ a` of hook `a` has total `1`;
* (rows) every row of hook `a` has total `(2a+1)/n`;
* (cells) the hooks cover every cell of the box exactly once;
* nonnegative values.

`HookDecomposition n` is stated exactly in this form; it is a hypothesis of the Kirwan-free
theorem (and it is verified from exact certificates for small `n` in
`STUProof/HookCertificates.lean`).

From a hook decomposition we build the *uniformisation* `unif n x lo hi` of the hook interval
`[lo, hi]`: values in `[0, 1]`, run totals `#{a ∈ [lo, hi] : a ≥ s}` and constant rows. For the
cross-shaped symmetric Young diagram `C(u, v) = [0,u]×[0,v] ∪ [0,v]×[0,u]` (`u ≤ v`), whose arm set
is `[v-u, v]`, this gives on every run a vector majorized by the run of the diagram
(`unif_smaj`).
-/

open Finset

noncomputable section

namespace STUProof

/-! ## Hook decompositions -/

/-- Run form of a hook decomposition of the `n`-box (the statement of `stu3/exact_hookdec.py`):
`x a s i ≥ 0` for hooks `a < n`, runs `s ≤ a` and positions `i < n - s`, with
* (run) `∑_i x a s i = 1` for all `a < n`, `s ≤ a`;
* (rows) `x a 0 r + ∑_{1 ≤ s ≤ a} ([r + s ≤ n-1] x a s r + [s ≤ r] x a s (r-s)) = (2a+1)/n`;
* (cells) `∑_{s ≤ a < n} x a s i = 1` for all `s < n`, `i < n - s`. -/
def IsHookDecomposition (n : ℕ) (x : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ a < n, ∀ s ≤ a, ∀ i < n - s, 0 ≤ x a s i) ∧
  (∀ a < n, ∀ s ≤ a, ∑ i ∈ range (n - s), x a s i = 1) ∧
  (∀ a < n, ∀ r < n, x a 0 r + ∑ s ∈ Icc 1 a,
    ((if r + s ≤ n - 1 then x a s r else 0) + (if s ≤ r then x a s (r - s) else 0)) =
      (2 * (a : ℝ) + 1) / n) ∧
  (∀ s < n, ∀ i < n - s, ∑ a ∈ Ico s n, x a s i = 1)

/-- **Hook Decomposition Lemma** for the `n`-box (independent of the spectrum `p`). -/
def HookDecomposition (n : ℕ) : Prop := ∃ x, IsHookDecomposition n x

/-! ## The symmetric cell form of a hook -/

/-- The symmetric cell form of hook `a` of a run-form hook decomposition (zero off the box and
off the runs `s ≤ a`). -/
def hookCell (n : ℕ) (x : ℕ → ℕ → ℕ → ℝ) (a i j : ℕ) : ℝ :=
  if i < n ∧ j < n then
    (if i ≤ j then (if j - i ≤ a then x a (j - i) i else 0)
      else (if i - j ≤ a then x a (i - j) j else 0))
  else 0

theorem hookCell_symm (n : ℕ) (x : ℕ → ℕ → ℕ → ℝ) (a i j : ℕ) :
    hookCell n x a i j = hookCell n x a j i := by
  rcases lt_trichotomy i j with h | h | h
  · have h1 : ¬ j ≤ i := by omega
    simp only [hookCell, h.le, h1, if_true, if_false, and_comm]
  · rw [h]
  · have h1 : ¬ i ≤ j := by omega
    simp only [hookCell, h.le, h1, if_true, if_false, and_comm]

theorem hookCell_upper (n : ℕ) (x : ℕ → ℕ → ℕ → ℝ) (a i s : ℕ) :
    hookCell n x a i (i + s) = if i + s < n ∧ s ≤ a then x a s i else 0 := by
  simp only [hookCell, Nat.le_add_right, if_true, Nat.add_sub_cancel_left]
  by_cases h1 : i + s < n
  · have h2 : i < n := by omega
    by_cases h3 : s ≤ a <;> simp [h1, h2, h3]
  · simp [h1]

variable {n : ℕ} {x : ℕ → ℕ → ℕ → ℝ}

theorem hookCell_nonneg (hx : IsHookDecomposition n x) {a : ℕ} (ha : a < n) (i j : ℕ) :
    0 ≤ hookCell n x a i j := by
  unfold hookCell
  split_ifs with h1 h2 h3 h4
  · exact hx.1 a ha _ h3 i (by omega)
  · exact le_refl _
  · exact hx.1 a ha _ h4 j (by omega)
  · exact le_refl _
  · exact le_refl _

theorem hookCell_run (hx : IsHookDecomposition n x) {a : ℕ} (ha : a < n) (s ℓ : ℕ)
    (hℓ : n - s ≤ ℓ) :
    ∑ i ∈ range ℓ, hookCell n x a i (i + s) = if s ≤ a then 1 else 0 := by
  simp only [hookCell_upper]
  split_ifs with hs
  · rw [← Finset.sum_filter]
    have hf : (range ℓ).filter (fun i => i + s < n ∧ s ≤ a) = range (n - s) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf]
    exact hx.2.1 a ha s hs
  · apply Finset.sum_eq_zero
    intro i _
    simp [hs]

/-- Row reindexing: a row of a symmetric configuration, split into the loop and the runs. -/
theorem sum_range_split_row (f : ℕ → ℝ) {r n : ℕ} (hr : r < n) :
    ∑ j ∈ range n, f j = f r + ∑ s ∈ Icc 1 (n - 1),
      ((if r + s < n then f (r + s) else 0) + (if s ≤ r then f (r - s) else 0)) := by
  have hA : ∑ s ∈ Icc 1 (n - 1), (if r + s < n then f (r + s) else 0) =
      ∑ j ∈ Ico (r + 1) n, f j := by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun s => r + s) (fun j => j - r) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_Icc] at hs
      simp only [Finset.mem_Ico]
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro s _
      simp
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      omega
    · intro s _
      rfl
  have hB : ∑ s ∈ Icc 1 (n - 1), (if s ≤ r then f (r - s) else 0) = ∑ j ∈ range r, f j := by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun s => r - s) (fun j => r - j) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_Icc] at hs
      simp only [Finset.mem_range]
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_Icc] at hs
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro s _
      rfl
  rw [Finset.sum_add_distrib, hA, hB, ← Finset.sum_range_add_sum_Ico _ (by omega : r + 1 ≤ n),
    Finset.sum_range_succ]
  ring

theorem hookCell_row (hx : IsHookDecomposition n x) {a : ℕ} (ha : a < n) {r : ℕ} (hr : r < n)
    (ℓ : ℕ) (hℓ : n ≤ ℓ) :
    ∑ j ∈ range ℓ, hookCell n x a r j = (2 * (a : ℝ) + 1) / n := by
  have hcut : ∑ j ∈ range ℓ, hookCell n x a r j = ∑ j ∈ range n, hookCell n x a r j := by
    rw [← Finset.sum_range_add_sum_Ico _ hℓ]
    have : ∑ j ∈ Ico n ℓ, hookCell n x a r j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      simp only [hookCell]
      rw [if_neg (by omega)]
    rw [this, add_zero]
  rw [hcut, sum_range_split_row _ hr, ← hx.2.2.1 a ha r hr]
  have e0 : hookCell n x a r r = x a 0 r := by
    have := hookCell_upper n x a r 0
    simp only [Nat.add_zero, hr, Nat.zero_le, and_self, if_true] at this
    exact this
  rw [e0]
  congr 1
  have hIcc : ∀ m, Icc 1 m = Ioc 0 m := fun m => by ext s; simp; omega
  rw [hIcc, hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) (by omega : a ≤ n - 1)]
  have hrest : ∑ s ∈ Ioc a (n - 1), ((if r + s < n then hookCell n x a r (r + s) else 0) +
      (if s ≤ r then hookCell n x a r (r - s) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finset.mem_Ioc] at hs
    rw [hookCell_upper]
    have h2 : s ≤ r → hookCell n x a r (r - s) = 0 := by
      intro hsr
      simp only [hookCell]
      split_ifs <;> first | rfl | omega
    by_cases hsr : s ≤ r
    · rw [h2 hsr]
      simp only [show ¬ s ≤ a by omega, and_false, if_false, ite_self, add_zero]
    · simp only [show ¬ s ≤ a by omega, and_false, if_false, ite_self, hsr, add_zero]
  rw [hrest, add_zero]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_Ioc] at hs
  congr 1
  · rw [hookCell_upper]
    by_cases h : r + s < n
    · simp [h, hs.2, show r + s ≤ n - 1 by omega]
    · simp [h, show ¬ r + s ≤ n - 1 by omega]
  · by_cases h : s ≤ r
    · have : hookCell n x a r (r - s) = x a s (r - s) := by
        rw [hookCell_symm]
        have := hookCell_upper n x a (r - s) s
        rw [show r - s + s = r by omega] at this
        rw [this, if_pos ⟨hr, hs.2⟩]
      simp [h, this]
    · simp [h]

theorem hookCell_cells (hx : IsHookDecomposition n x) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ∑ a ∈ range n, hookCell n x a i j = 1 := by
  wlog hij : i ≤ j generalizing i j
  · rw [Finset.sum_congr rfl (fun a _ => hookCell_symm n x a i j)]
    exact this hj hi (by omega)
  obtain ⟨s, rfl⟩ : ∃ s, j = i + s := ⟨j - i, by omega⟩
  simp only [hookCell_upper]
  rw [← Finset.sum_filter]
  have hf : (range n).filter (fun a => i + s < n ∧ s ≤ a) = Ico s n := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf]
  exact hx.2.2.2 s (by omega) i (by omega)

/-! ## Uniformisation of hook intervals -/

/-- Uniformisation of the hook interval `[lo, hi]` in the `n`-box. -/
def unif (n : ℕ) (x : ℕ → ℕ → ℕ → ℝ) (lo hi i j : ℕ) : ℝ :=
  ∑ a ∈ Icc lo hi, hookCell n x a i j

theorem unif_symm (lo hi i j : ℕ) : unif n x lo hi i j = unif n x lo hi j i :=
  Finset.sum_congr rfl (fun a _ => hookCell_symm n x a i j)

theorem unif_nonneg (hx : IsHookDecomposition n x) {lo hi : ℕ} (hhi : hi < n) (i j : ℕ) :
    0 ≤ unif n x lo hi i j :=
  Finset.sum_nonneg (fun a ha => hookCell_nonneg hx (by rw [Finset.mem_Icc] at ha; omega) i j)

theorem unif_le_one (hx : IsHookDecomposition n x) {lo hi : ℕ} (hhi : hi < n) (i j : ℕ) :
    unif n x lo hi i j ≤ 1 := by
  by_cases h : i < n ∧ j < n
  · rw [← hookCell_cells hx h.1 h.2]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_range]
      omega
    · intro a ha _
      exact hookCell_nonneg hx (Finset.mem_range.1 ha) i j
  · have : unif n x lo hi i j = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp only [hookCell]
      rw [if_neg h]
    rw [this]
    exact zero_le_one

theorem unif_run (hx : IsHookDecomposition n x) {lo hi : ℕ} (hhi : hi < n) (s ℓ : ℕ)
    (hℓ : n - s ≤ ℓ) :
    ∑ i ∈ range ℓ, unif n x lo hi i (i + s) = (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) := by
  simp only [unif]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a ha => hookCell_run hx (by rw [Finset.mem_Icc] at ha; omega)
    s ℓ hℓ)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem unif_row (hx : IsHookDecomposition n x) {lo hi : ℕ} (hhi : hi < n) (r ℓ : ℕ)
    (hℓ : n ≤ ℓ) :
    ∑ j ∈ range ℓ, unif n x lo hi r j =
      if r < n then (∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1)) / n else 0 := by
  simp only [unif]
  rw [Finset.sum_comm]
  split_ifs with hr
  · rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun a ha => hookCell_row hx (by rw [Finset.mem_Icc] at ha; omega)
      hr ℓ hℓ)
  · apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro j _
    simp only [hookCell]
    rw [if_neg (by omega)]

/-! ## Cross-shaped Young diagrams -/

/-- The indicator of the cross `[0,u]×[0,v] ∪ [0,v]×[0,u]` (for `u = v` the square `[0,u]²`). -/
def crossInd (u v i j : ℕ) : ℝ := if (i ≤ u ∧ j ≤ v) ∨ (i ≤ v ∧ j ≤ u) then 1 else 0

theorem crossInd_comm (u v i j : ℕ) : crossInd u v i j = crossInd v u i j := by
  unfold crossInd
  congr 1
  exact propext or_comm

theorem crossInd_run {u v : ℕ} (huv : u ≤ v) (i s : ℕ) :
    crossInd u v i (i + s) = if i < (if s ≤ v then min u (v - s) + 1 else 0) then 1 else 0 := by
  unfold crossInd
  split_ifs <;> first | rfl | omega

theorem card_filter_Icc_hook {u v : ℕ} (huv : u ≤ v) (s : ℕ) :
    ((Icc (v - u) v).filter (fun a => s ≤ a)).card = if s ≤ v then min u (v - s) + 1 else 0 := by
  have hf : (Icc (v - u) v).filter (fun a => s ≤ a) = Icc (max (v - u) s) v := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hf, Nat.card_Icc]
  split_ifs <;> omega

/-- **Uniformisation lemma for crosses.** On every run, the uniformisation of the arm interval
`[v-u, v]` in an `n`-box (`v < n ≤ d`) is majorized by the run of the cross `C(u, v)`. -/
theorem unif_smaj (hx : IsHookDecomposition n x) {u v d : ℕ} (huv : u ≤ v) (hvn : v < n)
    (hnd : n ≤ d) {s : ℕ} (hs : s < d) :
    SMaj (d - s) (fun i => unif n x (v - u) v i (i + s)) (fun i => crossInd u v i (i + s)) := by
  set N := if s ≤ v then min u (v - s) + 1 else 0 with hN
  have hNle : N ≤ d - s := by
    rw [hN]
    split_ifs <;> omega
  have h := smaj_zeroOne hNle (x := fun i => unif n x (v - u) v i (i + s))
    (fun i _ => unif_nonneg hx hvn _ _) (fun i _ => unif_le_one hx hvn _ _)
    (by rw [unif_run hx hvn s (d - s) (by omega), card_filter_Icc_hook huv s])
  refine h.congr (fun i _ => rfl) (fun i _ => ?_)
  rw [crossInd_run huv]

theorem ind_sum {d u : ℕ} (hu : u < d) :
    ∑ i ∈ range d, (if i ≤ u then (1 : ℝ) else 0) = u + 1 := by
  have := sum_range_indicator d (u + 1)
  simp only [Nat.lt_succ_iff] at this
  rw [this, min_eq_right (by omega)]
  push_cast
  ring

theorem crossInd_eq (m M i j : ℕ) : crossInd m M i j =
    (if i ≤ m then (1 : ℝ) else 0) * (if j ≤ M then 1 else 0) +
      (if i ≤ M then (1 : ℝ) else 0) * (if j ≤ m then 1 else 0) -
      (if i ≤ min m M then (1 : ℝ) else 0) * (if j ≤ min m M then 1 else 0) := by
  unfold crossInd
  rcases le_total m M with h | h
  · rw [min_eq_left h]
    split_ifs <;> (try norm_num) <;> omega
  · rw [min_eq_right h]
    split_ifs <;> (try norm_num) <;> omega

/-- Cell count of a cross equals the hook mass `∑_{a ∈ [v-u, v]} (2a+1)`. -/
theorem crossInd_sum {u v d : ℕ} (huv : u ≤ v) (hvd : v < d) :
    ∑ i ∈ range d, ∑ j ∈ range d, crossInd u v i j = ∑ a ∈ Icc (v - u) v, (2 * (a : ℝ) + 1) := by
  have hL : ∑ i ∈ range d, ∑ j ∈ range d, crossInd u v i j =
      ((u : ℝ) + 1) * (v + 1) + (v + 1) * (u + 1) - (u + 1) * (u + 1) := by
    simp only [crossInd_eq, min_eq_left huv, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul_sum, ind_sum (lt_of_le_of_lt huv hvd), ind_sum hvd]
  have hsq : ∀ m, ∑ a ∈ range m, (2 * (a : ℝ) + 1) = (m : ℝ) ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hR : ∑ a ∈ Icc (v - u) v, (2 * (a : ℝ) + 1) = ((v : ℝ) + 1) ^ 2 - ((v - u : ℕ) : ℝ) ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega : v - u ≤ v + 1), hsq, hsq]
    push_cast
    ring
  rw [hL, hR, Nat.cast_sub huv]
  ring

end STUProof
