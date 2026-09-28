import STUProof.STU

/-!
# Kirwan-free route, part 1: general tools

* `lc_reachable`: if a configuration `X` on `ι₁ × ι₂` is majorized by `λ` on every block of a
  partition into "LC sets" (sets with distinct rows and distinct columns), then some real
  orthogonal `O` gives `O diag(λ) Oᵀ` with marginals `diag(row sums of X)` and
  `diag(column sums of X)` (real Schur–Horn on each block, block-diagonal `O`).
* `SMaj`: majorization in subset form, `∑_{i∈S} x_i ≤ λ_0 + … + λ_{|S|-1}`; it is linear
  (superposition lemma `SMaj.add`, `SMaj.sum`, `SMaj.smul`) and implies `MajOn`.
* `tri_reachable`: the fixed tri-run structure (loop, upper runs `{(i, i+s)}`, lower runs).
* `ReachTri`: targets reachable inside the tri-run structure; closed under convex combinations.
-/

open Matrix Finset

noncomputable section

namespace STUProof

/-! ## Block-diagonal orthogonal matrices over the fibres of a labelling -/

section LC

variable {ι₁ ι₂ L : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  [Fintype L] [DecidableEq L]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
theorem blockDiagonal'_mem_orthogonalGroup {m' : L → Type*} [∀ ℓ, Fintype (m' ℓ)]
    [∀ ℓ, DecidableEq (m' ℓ)] {W : ∀ ℓ, Matrix (m' ℓ) (m' ℓ) ℝ}
    (hW : ∀ ℓ, W ℓ ∈ orthogonalGroup (m' ℓ) ℝ) :
    blockDiagonal' W ∈ orthogonalGroup (Σ ℓ, m' ℓ) ℝ := by
  rw [mem_orthogonalGroup_iff, blockDiagonal'_transpose, ← blockDiagonal'_mul]
  have h : (fun ℓ => W ℓ * (W ℓ)ᵀ) = (1 : ∀ ℓ, Matrix (m' ℓ) (m' ℓ) ℝ) :=
    funext fun ℓ => (mem_orthogonalGroup_iff _ _).1 (hW ℓ)
  rw [h, blockDiagonal'_one]

/-- **LC lemma.** Let `lab` partition `ι₁ × ι₂` into blocks with distinct rows and distinct
columns. If on every block the configuration `X` is majorized by `λ`, then some real orthogonal
`O` makes both marginals of `O diag(λ) Oᵀ` diagonal, with the row and column sums of `X`. -/
theorem lc_reachable (lab : ι₁ × ι₂ → L)
    (hcol : ∀ x y : ι₁ × ι₂, lab x = lab y → x.2 = y.2 → x.1 = y.1)
    (hrow : ∀ x y : ι₁ × ι₂, lab x = lab y → x.1 = y.1 → x.2 = y.2)
    (lam X : ι₁ × ι₂ → ℝ)
    (hmaj : ∀ ℓ, MajOn (Finset.univ.filter fun x => lab x = ℓ) X lam) :
    ∃ O ∈ orthogonalGroup (ι₁ × ι₂) ℝ,
      partialTraceB (O * diagonal lam * Oᵀ) = diagonal (fun a => ∑ b, X (a, b)) ∧
      partialTraceA (O * diagonal lam * Oᵀ) = diagonal (fun b => ∑ a, X (a, b)) := by
  have hSH : ∀ ℓ, ∃ G ∈ orthogonalGroup {x // lab x = ℓ} ℝ,
      ∀ i, (G * diagonal (fun x : {x // lab x = ℓ} => lam x) * Gᵀ) i i = X i := by
    intro ℓ
    apply schurHorn
    obtain ⟨h1, h2⟩ := hmaj ℓ
    have hmem : ∀ x, x ∈ (Finset.univ.filter fun x => lab x = ℓ) ↔ lab x = ℓ := by simp
    refine ⟨?_, fun t => ?_⟩
    · rw [← Finset.sum_subtype _ hmem X, ← Finset.sum_subtype _ hmem lam]
      exact h1
    · have h := h2 t
      rw [Finset.sum_subtype _ hmem (fun x => max (X x - t) 0),
        Finset.sum_subtype _ hmem (fun x => max (lam x - t) 0)] at h
      exact h
  choose W hWmem hW using hSH
  set e := Equiv.sigmaFiberEquiv lab with he
  set O := (blockDiagonal' W).submatrix e.symm e.symm with hO
  have hOmem : O ∈ orthogonalGroup (ι₁ × ι₂) ℝ :=
    submatrix_mem_orthogonalGroup (blockDiagonal'_mem_orthogonalGroup hWmem) e.symm
  have hstate : O * diagonal lam * Oᵀ =
      (blockDiagonal' fun ℓ => W ℓ * diagonal (fun x : {x // lab x = ℓ} => lam x) *
        (W ℓ)ᵀ).submatrix e.symm e.symm := by
    have hD : diagonal lam = (blockDiagonal' fun ℓ =>
        diagonal (fun x : {x // lab x = ℓ} => lam x)).submatrix e.symm e.symm := by
      rw [blockDiagonal'_diagonal, submatrix_diagonal_equiv]
      rfl
    rw [hO, hD, conj_submatrix, blockDiagonal'_transpose, ← blockDiagonal'_mul,
      ← blockDiagonal'_mul]
  have hdiag : ∀ x, (O * diagonal lam * Oᵀ) x x = X x := by
    intro x
    rw [hstate, submatrix_apply]
    show (blockDiagonal' fun ℓ => W ℓ * diagonal (fun x : {x // lab x = ℓ} => lam x) *
        (W ℓ)ᵀ) ⟨lab x, ⟨x, rfl⟩⟩ ⟨lab x, ⟨x, rfl⟩⟩ = X x
    rw [blockDiagonal'_apply_eq]
    exact hW (lab x) ⟨x, rfl⟩
  have hoff : ∀ x y, lab x ≠ lab y → (O * diagonal lam * Oᵀ) x y = 0 := by
    intro x y hxy
    rw [hstate, submatrix_apply]
    show (blockDiagonal' fun ℓ => W ℓ * diagonal (fun x : {x // lab x = ℓ} => lam x) *
        (W ℓ)ᵀ) ⟨lab x, ⟨x, rfl⟩⟩ ⟨lab y, ⟨y, rfl⟩⟩ = 0
    exact blockDiagonal'_apply_ne _ _ _ hxy
  refine ⟨O, hOmem, ?_, ?_⟩
  · ext a a'
    simp only [partialTraceB, of_apply, diagonal_apply]
    split_ifs with h
    · subst h
      exact Finset.sum_congr rfl (fun b _ => hdiag (a, b))
    · exact Finset.sum_eq_zero (fun b _ => hoff _ _ (fun hl => h (hcol (a, b) (a', b) hl rfl)))
  · ext b b'
    simp only [partialTraceA, of_apply, diagonal_apply]
    split_ifs with h
    · subst h
      exact Finset.sum_congr rfl (fun a _ => hdiag (a, b))
    · exact Finset.sum_eq_zero (fun a _ => hoff _ _ (fun hl => h (hrow (a, b) (a, b') hl rfl)))

end LC

/-! ## Majorization in subset form -/

/-- `SMaj ℓ x λ`: `x` is majorized by `λ` on `{0, …, ℓ-1}` in subset form: equal sums, and
`∑_{i∈S} x_i ≤ λ_0 + … + λ_{|S|-1}` for every `S`. For non-increasing `λ` this is the usual
majorization. -/
def SMaj (ℓ : ℕ) (x lam : ℕ → ℝ) : Prop :=
  ∑ i ∈ range ℓ, x i = ∑ i ∈ range ℓ, lam i ∧
    ∀ S ⊆ range ℓ, ∑ i ∈ S, x i ≤ ∑ i ∈ range S.card, lam i

theorem SMaj.add {ℓ : ℕ} {x₁ x₂ l₁ l₂ : ℕ → ℝ} (h₁ : SMaj ℓ x₁ l₁) (h₂ : SMaj ℓ x₂ l₂) :
    SMaj ℓ (fun i => x₁ i + x₂ i) (fun i => l₁ i + l₂ i) := by
  refine ⟨?_, fun S hS => ?_⟩
  · simp only [Finset.sum_add_distrib, h₁.1, h₂.1]
  · simp only [Finset.sum_add_distrib]
    exact add_le_add (h₁.2 S hS) (h₂.2 S hS)

theorem SMaj.smul {ℓ : ℕ} {x l : ℕ → ℝ} (h : SMaj ℓ x l) {c : ℝ} (hc : 0 ≤ c) :
    SMaj ℓ (fun i => c * x i) (fun i => c * l i) := by
  refine ⟨?_, fun S hS => ?_⟩
  · simp only [← Finset.mul_sum, h.1]
  · simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.2 S hS) hc

theorem SMaj.zero (ℓ : ℕ) : SMaj ℓ (fun _ => 0) (fun _ => 0) :=
  ⟨rfl, fun S _ => by simp⟩

theorem SMaj.sum {ℓ : ℕ} {ι : Type*} (T : Finset ι) {x l : ι → ℕ → ℝ}
    (h : ∀ t ∈ T, SMaj ℓ (x t) (l t)) :
    SMaj ℓ (fun i => ∑ t ∈ T, x t i) (fun i => ∑ t ∈ T, l t i) := by
  refine ⟨?_, fun S hS => ?_⟩
  · rw [Finset.sum_comm, Finset.sum_comm (s := range ℓ) (t := T)]
    exact Finset.sum_congr rfl (fun t ht => (h t ht).1)
  · rw [Finset.sum_comm, Finset.sum_comm (s := range S.card) (t := T)]
    exact Finset.sum_le_sum (fun t ht => (h t ht).2 S hS)

theorem SMaj.congr {ℓ : ℕ} {x x' l l' : ℕ → ℝ} (h : SMaj ℓ x l) (hx : ∀ i < ℓ, x i = x' i)
    (hl : ∀ i < ℓ, l i = l' i) : SMaj ℓ x' l' := by
  refine ⟨?_, fun S hS => ?_⟩
  · rw [← Finset.sum_congr rfl (fun i hi => hx i (Finset.mem_range.1 hi)),
      ← Finset.sum_congr rfl (fun i hi => hl i (Finset.mem_range.1 hi))]
    exact h.1
  · have hcard : S.card ≤ ℓ := by simpa using Finset.card_le_card hS
    rw [← Finset.sum_congr rfl (fun i hi => hx i (Finset.mem_range.1 (hS hi))),
      ← Finset.sum_congr rfl (fun i hi => hl i (by rw [Finset.mem_range] at hi; omega))]
    exact h.2 S hS

/-- Subset-form majorization implies hockey-stick majorization (`MajOn`). -/
theorem SMaj.majOn {ℓ : ℕ} {x l : ℕ → ℝ} (h : SMaj ℓ x l) : MajOn (range ℓ) x l := by
  refine ⟨h.1, fun t => ?_⟩
  set S := (range ℓ).filter (fun i => t < x i) with hS
  have hSsub : S ⊆ range ℓ := Finset.filter_subset _ _
  have hcard : S.card ≤ ℓ := by simpa using Finset.card_le_card hSsub
  have e1 : ∑ i ∈ range ℓ, max (x i - t) 0 = ∑ i ∈ S, x i - S.card * t := by
    have : ∀ i, max (x i - t) 0 = if t < x i then x i - t else 0 := by
      intro i
      split_ifs with hi
      · exact max_eq_left (by linarith)
      · exact max_eq_right (by linarith)
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_filter, ← hS,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∑ i ∈ range S.card, (l i - t) ≤ ∑ i ∈ range ℓ, max (l i - t) 0 := by
    calc ∑ i ∈ range S.card, (l i - t) ≤ ∑ i ∈ range S.card, max (l i - t) 0 :=
          Finset.sum_le_sum (fun i _ => le_max_left _ _)
      _ ≤ ∑ i ∈ range ℓ, max (l i - t) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hcard)
            (fun i _ _ => le_max_right _ _)
  have e3 : ∑ i ∈ range S.card, (l i - t) = ∑ i ∈ range S.card, l i - S.card * t := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 := h.2 S hSsub
  linarith

/-- A non-increasing vector is majorized by itself in subset form (top-`k` sums are initial
segments). -/
theorem smaj_self {ℓ : ℕ} {l : ℕ → ℝ} (hanti : ∀ i j, i ≤ j → j < ℓ → l j ≤ l i) :
    SMaj ℓ l l := by
  refine ⟨rfl, ?_⟩
  suffices H : ∀ n, ∀ S ⊆ range ℓ, S.card = n → ∑ i ∈ S, l i ≤ ∑ i ∈ range n, l i by
    intro S hS
    exact H _ S hS rfl
  intro n
  induction n with
  | zero =>
    intro S _ hS
    rw [Finset.card_eq_zero] at hS
    simp [hS]
  | succ n ih =>
    intro S hSsub hS
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    set m := S.max' hne with hm
    have hmS : m ∈ S := S.max'_mem hne
    have hmℓ : m < ℓ := Finset.mem_range.1 (hSsub hmS)
    have hmn : n ≤ m := by
      have hsub : S ⊆ range (m + 1) := fun i hi =>
        Finset.mem_range.2 (Nat.lt_succ_of_le (S.le_max' i hi))
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    rw [← Finset.add_sum_erase S _ hmS, Finset.sum_range_succ, add_comm (∑ i ∈ range n, l i)]
    apply add_le_add (hanti n m hmn hmℓ)
    apply ih (S.erase m) ((Finset.erase_subset _ _).trans hSsub)
    rw [Finset.card_erase_of_mem hmS, hS]
    rfl

theorem sum_range_indicator (n N : ℕ) :
    ∑ i ∈ range n, (if i < N then (1 : ℝ) else 0) = (min n N : ℕ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one]
  congr 1
  have : (range n).filter (fun i => i < N) = range (min n N) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-- The `0/1` lemma: values in `[0, 1]` with total `N` are majorized by `(1, …, 1, 0, …, 0)`
(`N` ones). -/
theorem smaj_zeroOne {ℓ N : ℕ} (hN : N ≤ ℓ) {x : ℕ → ℝ} (h0 : ∀ i < ℓ, 0 ≤ x i)
    (h1 : ∀ i < ℓ, x i ≤ 1) (hs : ∑ i ∈ range ℓ, x i = N) :
    SMaj ℓ x (fun i => if i < N then 1 else 0) := by
  refine ⟨?_, fun S hS => ?_⟩
  · rw [hs, sum_range_indicator, min_eq_right hN]
  · rw [sum_range_indicator, Nat.cast_min]
    apply le_min
    · calc ∑ i ∈ S, x i ≤ ∑ _i ∈ S, (1 : ℝ) :=
            Finset.sum_le_sum (fun i hi => h1 i (Finset.mem_range.1 (hS hi)))
        _ = S.card := by simp
    · calc ∑ i ∈ S, x i ≤ ∑ i ∈ range ℓ, x i :=
            Finset.sum_le_sum_of_subset_of_nonneg hS
              (fun i hi _ => h0 i (Finset.mem_range.1 hi))
        _ = N := hs

/-! ## The tri-run structure -/

/-- Label of the cell `(i, j)` of `Fin d × Fin d`: its diagonal, encoded as `d + j - i`. The
blocks are the loop (`d`), the upper runs `{(i, i+s)}` (`d + s`) and the lower runs (`d - s`). -/
def triLab {d : ℕ} (x : Fin d × Fin d) : Fin (2 * d) :=
  ⟨d + x.2 - x.1, by have := x.1.isLt; have := x.2.isLt; omega⟩

theorem triLab_val {d : ℕ} (x : Fin d × Fin d) : (triLab x : ℕ) = d + x.2 - x.1 := rfl

theorem sum_triLab_upper {d : ℕ} (g : ℕ → ℕ → ℝ) {s : ℕ} (hs : s < d) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin d × Fin d => (triLab x : ℕ) = d + s),
      g x.1 x.2 = ∑ i ∈ range (d - s), g i (i + s) := by
  have hmem : ∀ x : Fin d × Fin d,
      x ∈ Finset.univ.filter (fun x : Fin d × Fin d => (triLab x : ℕ) = d + s) ↔
        (x.2 : ℕ) = x.1 + s := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [triLab_val]
    have := x.1.isLt
    omega
  refine Finset.sum_bij' (fun x _ => (x.1 : ℕ))
    (fun i hi => (((⟨i, by rw [Finset.mem_range] at hi; omega⟩ : Fin d),
      (⟨i + s, by rw [Finset.mem_range] at hi; omega⟩ : Fin d)) : Fin d × Fin d))
    ?hi ?hj ?li ?ri ?h
  case hi =>
    intro x hx
    rw [hmem] at hx
    rw [Finset.mem_range]
    have := x.2.isLt
    omega
  case hj =>
    intro i hi
    rw [hmem]
  case li =>
    intro x hx
    rw [hmem] at hx
    ext
    · rfl
    · exact hx.symm
  case ri =>
    intro i hi
    rfl
  case h =>
    intro x hx
    rw [hmem] at hx
    rw [hx]

theorem sum_triLab_lower {d : ℕ} (g : ℕ → ℕ → ℝ) {s : ℕ} (hs1 : 1 ≤ s) (hs : s < d) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin d × Fin d => (triLab x : ℕ) = d - s),
      g x.1 x.2 = ∑ i ∈ range (d - s), g (i + s) i := by
  have hmem : ∀ x : Fin d × Fin d,
      x ∈ Finset.univ.filter (fun x : Fin d × Fin d => (triLab x : ℕ) = d - s) ↔
        (x.1 : ℕ) = x.2 + s := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [triLab_val]
    have := x.1.isLt
    have := x.2.isLt
    omega
  refine Finset.sum_bij' (fun x _ => (x.2 : ℕ))
    (fun i hi => (((⟨i + s, by rw [Finset.mem_range] at hi; omega⟩ : Fin d),
      (⟨i, by rw [Finset.mem_range] at hi; omega⟩ : Fin d)) : Fin d × Fin d))
    ?hi ?hj ?li ?ri ?h
  case hi =>
    intro x hx
    rw [hmem] at hx
    rw [Finset.mem_range]
    have := x.1.isLt
    omega
  case hj =>
    intro i hi
    rw [hmem]
  case li =>
    intro x hx
    rw [hmem] at hx
    ext
    · exact hx.symm
    · rfl
  case ri =>
    intro i hi
    rfl
  case h =>
    intro x hx
    rw [hmem] at hx
    rw [hx]

theorem sum_triLab_zero {d : ℕ} (g : ℕ → ℕ → ℝ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin d × Fin d => (triLab x : ℕ) = 0), g x.1 x.2 = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [triLab_val] at hx
  have := x.1.isLt
  omega

theorem majOn_transport {d ℓ : ℕ} {A : Finset (Fin d × Fin d)} {a b : ℕ → ℕ}
    (hT : ∀ g : ℕ → ℕ → ℝ, ∑ x ∈ A, g x.1 x.2 = ∑ i ∈ range ℓ, g (a i) (b i))
    {F Λ : ℕ → ℕ → ℝ}
    (h : MajOn (range ℓ) (fun i => F (a i) (b i)) (fun i => Λ (a i) (b i))) :
    MajOn A (fun x => F x.1 x.2) (fun x => Λ x.1 x.2) := by
  refine ⟨?_, fun t => ?_⟩
  · rw [hT F, hT Λ]
    exact h.1
  · rw [hT (fun i j => max (F i j - t) 0), hT (fun i j => max (Λ i j - t) 0)]
    exact h.2 t

/-- **Reachability in the tri-run structure.** A symmetric configuration `F` whose every run is
majorized by the corresponding run of `p ⊗ p` yields a real orthogonal `O` such that both
marginals of `O diag(p ⊗ p) Oᵀ` are `diag(row sums of F)`. -/
theorem tri_reachable {d : ℕ} (p : Fin d → ℝ) (F : ℕ → ℕ → ℝ) (hsym : ∀ i j, F i j = F j i)
    (hmaj : ∀ s < d, MajOn (range (d - s)) (fun i => F i (i + s))
      (fun i => extN p i * extN p (i + s))) :
    ∃ O ∈ orthogonalGroup (Fin d × Fin d) ℝ,
      partialTraceB (O * diagonal (fun x => p x.1 * p x.2) * Oᵀ) =
        diagonal (fun a : Fin d => ∑ j ∈ range d, F a j) ∧
      partialTraceA (O * diagonal (fun x => p x.1 * p x.2) * Oᵀ) =
        diagonal (fun a : Fin d => ∑ j ∈ range d, F a j) := by
  have hlam : (fun x : Fin d × Fin d => p x.1 * p x.2) =
      fun x => extN p x.1 * extN p x.2 := by
    funext x
    rw [extN_lt p x.1.isLt, extN_lt p x.2.isLt]
  have hblock : ∀ ℓ : Fin (2 * d), MajOn (Finset.univ.filter fun x => triLab x = ℓ)
      (fun x : Fin d × Fin d => F x.1 x.2) (fun x => extN p x.1 * extN p x.2) := by
    intro ℓ
    have hfilt : (Finset.univ.filter fun x : Fin d × Fin d => triLab x = ℓ) =
        Finset.univ.filter fun x : Fin d × Fin d => (triLab x : ℕ) = ℓ := by
      ext x
      simp [Fin.ext_iff]
    rw [hfilt]
    have hℓ := ℓ.isLt
    rcases Nat.lt_or_ge (ℓ : ℕ) d with h | h
    · rcases Nat.eq_zero_or_pos (ℓ : ℕ) with h0 | h0
      · rw [h0]
        refine ⟨?_, fun t => ?_⟩
        · rw [sum_triLab_zero F, sum_triLab_zero (fun i j => extN p i * extN p j)]
        · rw [sum_triLab_zero (fun i j => max (F i j - t) 0),
            sum_triLab_zero (fun i j => max (extN p i * extN p j - t) 0)]
      · obtain ⟨s, hsdef⟩ : ∃ s, s = d - (ℓ : ℕ) := ⟨_, rfl⟩
        have hs1 : 1 ≤ s := by omega
        have hs : s < d := by omega
        have heq : (ℓ : ℕ) = d - s := by omega
        rw [heq]
        apply majOn_transport (F := F) (Λ := fun i j => extN p i * extN p j)
          (fun g => sum_triLab_lower g hs1 hs)
        have e1 : (fun i => F (i + s) i) = fun i => F i (i + s) :=
          funext fun i => hsym _ _
        have e2 : (fun i => extN p (i + s) * extN p i) = fun i => extN p i * extN p (i + s) :=
          funext fun i => mul_comm _ _
        show MajOn (range (d - s)) (fun i => F (i + s) i) (fun i => extN p (i + s) * extN p i)
        rw [e1, e2]
        exact hmaj s hs
    · have hs : (ℓ : ℕ) - d < d := by omega
      have heq : (ℓ : ℕ) = d + ((ℓ : ℕ) - d) := by omega
      rw [heq]
      exact majOn_transport (F := F) (Λ := fun i j => extN p i * extN p j)
        (fun g => sum_triLab_upper g hs) (hmaj _ hs)
  have hcol : ∀ x y : Fin d × Fin d, triLab x = triLab y → x.2 = y.2 → x.1 = y.1 := by
    intro x y hxy h2
    rw [Fin.ext_iff, triLab_val, triLab_val] at hxy
    rw [Fin.ext_iff] at h2 ⊢
    have := x.1.isLt
    have := y.1.isLt
    omega
  have hrow : ∀ x y : Fin d × Fin d, triLab x = triLab y → x.1 = y.1 → x.2 = y.2 := by
    intro x y hxy h1
    rw [Fin.ext_iff, triLab_val, triLab_val] at hxy
    rw [Fin.ext_iff] at h1 ⊢
    have := x.1.isLt
    have := y.1.isLt
    omega
  obtain ⟨O, hO, hB, hA⟩ := lc_reachable triLab hcol hrow
    (fun x => extN p x.1 * extN p x.2) (fun x => F x.1 x.2) hblock
  refine ⟨O, hO, ?_, ?_⟩
  · rw [hlam, hB]
    congr 1
    funext a
    exact Fin.sum_univ_eq_sum_range (fun j => F a j) d
  · rw [hlam, hA]
    congr 1
    funext b
    rw [← Fin.sum_univ_eq_sum_range (fun j => F b j) d]
    exact Finset.sum_congr rfl (fun a _ => hsym _ _)

/-- Targets `q` reachable inside the tri-run structure for the weights `P ⊗ P`: some symmetric
configuration has every run majorized (subset form) by the run of `P ⊗ P`, and rows `q`. -/
def ReachTri (d : ℕ) (P q : ℕ → ℝ) : Prop :=
  ∃ F : ℕ → ℕ → ℝ, (∀ i j, F i j = F j i) ∧
    (∀ s < d, SMaj (d - s) (fun i => F i (i + s)) (fun i => P i * P (i + s))) ∧
    ∀ r < d, ∑ j ∈ range d, F r j = q r

/-- **Convexity for the fixed structure.** -/
theorem ReachTri.convex {d K : ℕ} {P μ : ℕ → ℝ} {q : ℕ → ℕ → ℝ}
    (hμ0 : ∀ k < K, 0 ≤ μ k) (hμ1 : ∑ k ∈ range K, μ k = 1)
    (h : ∀ k < K, ReachTri d P (q k)) :
    ReachTri d P (fun r => ∑ k ∈ range K, μ k * q k r) := by
  have h' : ∀ k, ∃ F : ℕ → ℕ → ℝ, k < K → ((∀ i j, F i j = F j i) ∧
      (∀ s < d, SMaj (d - s) (fun i => F i (i + s)) (fun i => P i * P (i + s))) ∧
      ∀ r < d, ∑ j ∈ range d, F r j = q k r) := by
    intro k
    by_cases hk : k < K
    · obtain ⟨F, hF⟩ := h k hk
      exact ⟨F, fun _ => hF⟩
    · exact ⟨0, fun h' => absurd h' hk⟩
  choose F hF using h'
  refine ⟨fun i j => ∑ k ∈ range K, μ k * F k i j, ?_, ?_, ?_⟩
  · intro i j
    exact Finset.sum_congr rfl (fun k hk => by rw [(hF k (Finset.mem_range.1 hk)).1 i j])
  · intro s hs
    have := SMaj.sum (range K) (fun k hk =>
      ((hF k (Finset.mem_range.1 hk)).2.1 s hs).smul (hμ0 k (Finset.mem_range.1 hk)))
    refine this.congr (fun i _ => rfl) (fun i _ => ?_)
    rw [← Finset.sum_mul, hμ1, one_mul]
  · intro r hr
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [← Finset.mul_sum, (hF k (Finset.mem_range.1 hk)).2.2 r hr]

/-- A target reachable in the tri-run structure is a symmetric pair of marginals, realized by a
real orthogonal matrix. -/
theorem ReachTri.orthogonal {d : ℕ} {p q : Fin d → ℝ} (h : ReachTri d (extN p) (extN q)) :
    ∃ O ∈ orthogonalGroup (Fin d × Fin d) ℝ,
      partialTraceB (O * diagonal (fun x => p x.1 * p x.2) * Oᵀ) = diagonal q ∧
      partialTraceA (O * diagonal (fun x => p x.1 * p x.2) * Oᵀ) = diagonal q := by
  obtain ⟨F, hsym, hmaj, hrow⟩ := h
  obtain ⟨O, hO, hB, hA⟩ := tri_reachable p F hsym (fun s hs => (hmaj s hs).majOn)
  have hq : (fun a : Fin d => ∑ j ∈ range d, F a j) = q := by
    funext a
    rw [hrow a a.isLt, extN_lt q a.isLt]
  refine ⟨O, hO, ?_, ?_⟩
  · rw [hB, hq]
  · rw [hA, hq]

/-! ## Lemma T: thermal targets are convex combinations of clipped points -/

/-- Chord slopes of `g` along `P`: `N_0 = 0`; for `1 ≤ k < d`, `N_k` is the slope of `g` on
`[P_k, P_{k-1}]` (or `N_{k-1}` if `P_k = P_{k-1}`); `N_d = g(P_{d-1}) / P_{d-1}`. -/
def slopeSeq (P : ℕ → ℝ) (g : ℝ → ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if k + 1 < d then
      (if P k = P (k + 1) then slopeSeq P g d k
        else (g (P k) - g (P (k + 1))) / (P k - P (k + 1)))
    else g (P (d - 1)) / P (d - 1)

section LemmaT

variable {P : ℕ → ℝ} {g : ℝ → ℝ} {d : ℕ}

theorem slopeSeq_mul {k : ℕ} (hk : k + 1 < d) :
    slopeSeq P g d (k + 1) * (P k - P (k + 1)) = g (P k) - g (P (k + 1)) := by
  simp only [slopeSeq, if_pos hk]
  split_ifs with h
  · rw [h, sub_self, mul_zero, sub_self]
  · rw [div_mul_cancel₀ _ (sub_ne_zero.2 h)]

theorem slopeSeq_last (hd : 0 < d) (hpos : P (d - 1) ≠ 0) :
    slopeSeq P g d d * P (d - 1) = g (P (d - 1)) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [slopeSeq, lt_irrefl, if_false]
  rw [div_mul_cancel₀ _ hpos]

variable (hanti : ∀ i j, i ≤ j → j < d → P j ≤ P i) (hpos : ∀ i < d, 0 < P i)
  (hg : ConcaveOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))

include hanti hpos hg hgm in
theorem slopeSeq_le_chord : ∀ k < d, ∀ x, 0 ≤ x → x < P k →
    slopeSeq P g d k ≤ (g (P k) - g x) / (P k - x) := by
  intro k
  induction k with
  | zero =>
    intro _ x hx0 hx
    simp only [slopeSeq]
    apply div_nonneg
    · exact sub_nonneg.2 (hgm (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (by linarith)) hx.le)
    · linarith
  | succ k ih =>
    intro hk x hx0 hx
    simp only [slopeSeq, if_pos hk]
    split_ifs with h
    · have := ih (by omega) x hx0 (by rw [h]; exact hx)
      rwa [h] at this
    · have hlt : P (k + 1) < P k := lt_of_le_of_ne (hanti k (k + 1) (by omega) hk) (Ne.symm h)
      exact hg.slope_anti_adjacent (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (hpos k (by omega)).le)
        hx hlt

include hanti hpos hg hgm in
theorem slopeSeq_mono (hg0 : 0 ≤ g 0) : ∀ k < d, slopeSeq P g d k ≤ slopeSeq P g d (k + 1) := by
  intro k hk
  have inv := slopeSeq_le_chord hanti hpos hg hgm k hk
  by_cases hk1 : k + 1 < d
  · simp only [slopeSeq, if_pos hk1]
    split_ifs with h
    · exact le_refl _
    · have hlt : P (k + 1) < P k :=
        lt_of_le_of_ne (hanti k (k + 1) (by omega) hk1) (Ne.symm h)
      exact inv (P (k + 1)) (hpos (k + 1) hk1).le hlt
  · have hkd : k = d - 1 := by omega
    simp only [slopeSeq, if_neg hk1]
    have h0 := inv 0 le_rfl (hpos k hk)
    rw [sub_zero] at h0
    calc slopeSeq P g d k ≤ g (P k) / P k - g 0 / P k := by rw [← sub_div]; exact h0
      _ ≤ g (P k) / P k := by
          have : 0 ≤ g 0 / P k := div_nonneg hg0 (hpos k hk).le
          linarith
      _ = g (P (d - 1)) / P (d - 1) := by rw [hkd]

include hpos in
theorem slopeSeq_tail (hd : 0 < d) : ∀ m i, i + m + 1 = d →
    slopeSeq P g d i * P i + ∑ k ∈ Ico i d, (slopeSeq P g d (k + 1) - slopeSeq P g d k) * P k =
      g (P i) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hid : i = d - 1 := by omega
    rw [show d = i + 1 by omega, Nat.Ico_succ_singleton, Finset.sum_singleton]
    have := slopeSeq_last (P := P) (g := g) hd (hpos (d - 1) (by omega)).ne'
    rw [← hid, show d = i + 1 by omega] at this
    rw [← this]
    ring
  | succ m ih =>
    intro i hi
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i < d)]
    have h1 := ih (i + 1) (by omega)
    have h2 := slopeSeq_mul (P := P) (g := g) (k := i) (by omega : i + 1 < d)
    linear_combination h1 + h2

include hanti hpos in
theorem slopeSeq_sum (hd : 0 < d) : ∀ i < d,
    ∑ k ∈ range d, (slopeSeq P g d (k + 1) - slopeSeq P g d k) * min (P i) (P k) = g (P i) := by
  intro i hi
  rw [← Finset.sum_range_add_sum_Ico _ hi.le]
  have e1 : ∑ k ∈ range i, (slopeSeq P g d (k + 1) - slopeSeq P g d k) * min (P i) (P k) =
      slopeSeq P g d i * P i := by
    rw [Finset.sum_congr rfl (fun k hk => by
      rw [min_eq_left (hanti k i (by rw [Finset.mem_range] at hk; omega) hi)]),
      ← Finset.sum_mul, Finset.sum_range_sub (fun k => slopeSeq P g d k)]
    simp [slopeSeq]
  have e2 : ∑ k ∈ Ico i d, (slopeSeq P g d (k + 1) - slopeSeq P g d k) * min (P i) (P k) =
      ∑ k ∈ Ico i d, (slopeSeq P g d (k + 1) - slopeSeq P g d k) * P k := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_Ico] at hk
    rw [min_eq_right (hanti i k hk.1 hk.2)]
  rw [e1, e2]
  exact slopeSeq_tail hpos hd (d - 1 - i) i (by omega)

include hanti hpos hg hgm in
/-- **Lemma T (abstract).** For a concave, monotone `g` with `g 0 ≥ 0` and a positive
non-increasing `P`, `g(P_i) = ∑_k ν_k min(P_i, P_k)` with `ν_k ≥ 0`. -/
theorem lemmaT (hd : 0 < d) (hg0 : 0 ≤ g 0) :
    ∃ ν : ℕ → ℝ, (∀ k < d, 0 ≤ ν k) ∧
      ∀ i < d, ∑ k ∈ range d, ν k * min (P i) (P k) = g (P i) :=
  ⟨fun k => slopeSeq P g d (k + 1) - slopeSeq P g d k,
    fun k hk => sub_nonneg.2 (slopeSeq_mono hanti hpos hg hgm hg0 k hk),
    slopeSeq_sum hanti hpos hd⟩

end LemmaT

/-- The normalization `Z_k = ∑_j min(P_j, P_k)` of the clipped point `w_k = min(P, P_k) / Z_k`. -/
def clipZ (P : ℕ → ℝ) (d k : ℕ) : ℝ := ∑ j ∈ range d, min (P j) (P k)

theorem gibbs_pos {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (β : ℝ) (i : Fin d) :
    0 < gibbs E β i :=
  div_pos (Real.exp_pos _) (gibbs_Z_pos hd E β)

/-- `Gibbs(β') ∝ Gibbs(β)^{β'/β}`. -/
theorem gibbs_rpow {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) {β β' : ℝ} (hβ : 0 < β) (i : Fin d) :
    gibbs E β' i = gibbs E β i ^ (β' / β) / ∑ j, gibbs E β j ^ (β' / β) := by
  have hZ := gibbs_Z_pos hd E β
  have key : ∀ j, gibbs E β j ^ (β' / β) =
      Real.exp (-β' * E j) / (∑ l, Real.exp (-β * E l)) ^ (β' / β) := by
    intro j
    unfold gibbs
    rw [Real.div_rpow (Real.exp_pos _).le hZ.le, ← Real.exp_mul]
    congr 2
    field_simp
  simp only [key]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ (Real.rpow_pos_of_pos hZ _).ne']
  rfl

/-- **Lemma T (thermal form).** `Gibbs(β')` is a convex combination of the clipped points
`w_k = min(p, p_k) / Z_k` of `p = Gibbs(β)`. -/
theorem thermal_clip_weights {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ}
    (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ μ : ℕ → ℝ, (∀ k < d, 0 ≤ μ k) ∧ ∑ k ∈ range d, μ k = 1 ∧
      ∀ i < d, extN (gibbs E β') i = ∑ k ∈ range d, μ k *
        (min (extN (gibbs E β) i) (extN (gibbs E β) k) / clipZ (extN (gibbs E β)) d k) := by
  set p := gibbs E β with hp
  set P := extN p with hP
  set t := β' / β with ht
  have ht0 : 0 ≤ t := div_nonneg h0 hβ.le
  have ht1 : t ≤ 1 := (div_le_one hβ).2 h1
  have hpA : Antitone p := gibbs_antitone E hE hβ.le
  have hanti : ∀ i j, i ≤ j → j < d → P j ≤ P i := by
    intro i j hij hj
    rw [hP, extN_lt p hj, extN_lt p (lt_of_le_of_lt hij hj)]
    exact hpA (Fin.mk_le_mk.2 hij)
  have hpos : ∀ i < d, 0 < P i := by
    intro i hi
    rw [hP, extN_lt p hi]
    exact gibbs_pos hd E β _
  set g : ℝ → ℝ := fun x => x ^ t with hg
  have hgc : ConcaveOn ℝ (Set.Ici 0) g := Real.concaveOn_rpow ht0 ht1
  have hgm : MonotoneOn g (Set.Ici 0) := fun x hx y _ hxy => Real.rpow_le_rpow hx hxy ht0
  have hg0 : 0 ≤ g 0 := Real.rpow_nonneg le_rfl t
  obtain ⟨ν, hν0, hν⟩ := lemmaT hanti hpos hgc hgm hd hg0
  set S := ∑ j ∈ range d, g (P j) with hS
  have hSpos : 0 < S :=
    Finset.sum_pos (fun j hj => Real.rpow_pos_of_pos (hpos j (Finset.mem_range.1 hj)) t)
      ⟨0, Finset.mem_range.2 hd⟩
  have hZpos : ∀ k < d, 0 < clipZ P d k := by
    intro k hk
    have : min (P k) (P k) ≤ clipZ P d k :=
      Finset.single_le_sum (f := fun j => min (P j) (P k))
        (fun j hj => le_min (hpos j (Finset.mem_range.1 hj)).le (hpos k hk).le)
        (Finset.mem_range.2 hk)
    rw [min_self] at this
    linarith [hpos k hk]
  refine ⟨fun k => ν k * clipZ P d k / S, fun k hk =>
    div_nonneg (mul_nonneg (hν0 k hk) (hZpos k hk).le) hSpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_eq_one_iff_eq hSpos.ne']
    simp only [clipZ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← hν j (Finset.mem_range.1 hj)]
  · intro i hi
    have e1 : ∑ k ∈ range d, ν k * clipZ P d k / S * (min (P i) (P k) / clipZ P d k) =
        (∑ k ∈ range d, ν k * min (P i) (P k)) / S := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have := (hZpos k (Finset.mem_range.1 hk)).ne'
      field_simp
    rw [e1, hν i hi, hP, extN_lt _ hi, extN_lt _ hi, gibbs_rpow hd E hβ]
    congr 1
    rw [hS, ← Fin.sum_univ_eq_sum_range (fun j => g (extN p j)) d]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [extN_lt p j.isLt]

end STUProof
