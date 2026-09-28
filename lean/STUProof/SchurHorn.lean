import Mathlib

/-!
# The real Schur–Horn theorem (existence direction)

If `x ≺ λ` (`x` is majorized by `λ`), then there is a real orthogonal matrix `G` such that the
diagonal of `G * diagonal λ * Gᵀ` is `x`.

## Majorization without sorting

We use the "hockey-stick" characterization of majorization, which needs no sorting:
`x ≺ y` on a finite set `U` iff `∑_{i∈U} x_i = ∑_{i∈U} y_i` and, for every real `t`,
`∑_{i∈U} (x_i - t)⁺ ≤ ∑_{i∈U} (y_i - t)⁺` (`MajOn`).

## Proof (Chan–Li style induction)

We keep a matrix `M` that is diagonal on the set `U` of unfinished indices. Pick `i₀ ∈ U` with
the largest target `a = x i₀`, the index `j₁ ∈ U` with the largest diagonal entry `m₁`, and among
the other indices of `U` with diagonal entry `≤ a` the index `j₂` with the largest entry `m₂`.
A Givens rotation in the plane `(j₁, j₂)` puts `a` at `(j₁, j₁)` and `m₁ + m₂ - a` at `(j₂, j₂)`,
and keeps `M` diagonal on `U \ {j₁}`. A transposition moves the finished entry to `i₀`.
The combinatorial lemma `maj_step` shows that the targets on `U \ {i₀}` are still majorized by the
new diagonal. We then recurse.
-/

open Matrix Finset

noncomputable section

namespace STUProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `MajOn U x y`: `x` is majorized by `y` on the finite set `U` (hockey-stick form). -/
def MajOn (U : Finset ι) (x y : ι → ℝ) : Prop :=
  ∑ i ∈ U, x i = ∑ i ∈ U, y i ∧
    ∀ t : ℝ, ∑ i ∈ U, max (x i - t) 0 ≤ ∑ i ∈ U, max (y i - t) 0

/-! ## The combinatorial step -/

omit [Fintype ι] in
/-- The key majorization step. `a = x i₀` is the largest target, `m₁ = y j₁ ≥ a ≥ m₂ = y j₂`,
and no other value `y j` lies strictly between `m₂` and `a`. Removing `i₀` from the targets and
replacing `m₁, m₂` by `m₁ + m₂ - a` preserves the hockey-stick inequalities. -/
theorem maj_step (U : Finset ι) (x y : ι → ℝ) (i₀ j₁ j₂ : ι)
    (hi₀ : i₀ ∈ U) (hj₁ : j₁ ∈ U) (hj₂ : j₂ ∈ U) (h12 : j₁ ≠ j₂)
    (hxmax : ∀ i ∈ U, x i ≤ x i₀) (ha1 : x i₀ ≤ y j₁) (ha2 : y j₂ ≤ x i₀)
    (hgap : ∀ j ∈ U, j ≠ j₁ → j ≠ j₂ → y j ≤ y j₂ ∨ x i₀ ≤ y j)
    (hmaj : ∀ t, ∑ i ∈ U, max (x i - t) 0 ≤ ∑ i ∈ U, max (y i - t) 0) (t : ℝ) :
    ∑ i ∈ U.erase i₀, max (x i - t) 0 ≤
      ∑ j ∈ (U.erase j₁).erase j₂, max (y j - t) 0 + max (y j₁ + y j₂ - x i₀ - t) 0 := by
  set a := x i₀ with ha
  set m₁ := y j₁ with hm₁
  set m₂ := y j₂ with hm₂
  set V := (U.erase j₁).erase j₂ with hV
  have hj₂' : j₂ ∈ U.erase j₁ := Finset.mem_erase.2 ⟨h12.symm, hj₂⟩
  have hxU : ∀ s, ∑ i ∈ U, max (x i - s) 0 =
      max (a - s) 0 + ∑ i ∈ U.erase i₀, max (x i - s) 0 := fun s =>
    (Finset.add_sum_erase U (fun i => max (x i - s) 0) hi₀).symm
  have hyU : ∀ s, ∑ j ∈ U, max (y j - s) 0 =
      max (m₁ - s) 0 + (max (m₂ - s) 0 + ∑ j ∈ V, max (y j - s) 0) := by
    intro s
    rw [Finset.add_sum_erase (U.erase j₁) (fun j => max (y j - s) 0) hj₂',
      Finset.add_sum_erase U (fun j => max (y j - s) 0) hj₁]
  have hVnn : 0 ≤ ∑ j ∈ V, max (y j - t) 0 := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have hmax0 := le_max_right (m₁ + m₂ - a - t) 0
  have hmax1 := le_max_left (m₁ + m₂ - a - t) 0
  rcases le_or_gt a t with hat | hta
  · -- all remaining targets are `≤ t`
    have h0 : ∑ i ∈ U.erase i₀, max (x i - t) 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have := hxmax i (Finset.mem_of_mem_erase hi)
      exact max_eq_right (by linarith)
    rw [h0]
    linarith
  rcases le_or_gt t m₂ with htm | hmt
  · have h1 := hmaj t
    rw [hxU, hyU] at h1
    have e1 : max (a - t) 0 = a - t := max_eq_left (by linarith)
    have e2 : max (m₁ - t) 0 = m₁ - t := max_eq_left (by linarith)
    have e3 : max (m₂ - t) 0 = m₂ - t := max_eq_left (by linarith)
    rw [e1, e2, e3] at h1
    linarith
  · -- the delicate range `m₂ < t < a`
    set G := V.filter (fun j => a ≤ y j) with hG
    have hVG : ∀ s, m₂ ≤ s → s ≤ a → ∑ j ∈ V, max (y j - s) 0 = ∑ j ∈ G, (y j - s) := by
      intro s hs1 hs2
      rw [hG, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      have hjU : j ∈ U := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)
      have hj1 : j ≠ j₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      have hj2 : j ≠ j₂ := Finset.ne_of_mem_erase hj
      split_ifs with h
      · exact max_eq_left (by linarith)
      · rcases hgap j hjU hj1 hj2 with h' | h'
        · exact max_eq_right (by linarith)
        · exact absurd h' h
    set S := (U.erase i₀).filter (fun i => t < x i) with hS
    have hLS : ∑ i ∈ U.erase i₀, max (x i - t) 0 = ∑ i ∈ S, (x i - t) := by
      rw [hS, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · exact max_eq_left (by linarith)
      · exact max_eq_right (by linarith)
    rw [hLS, hVG t hmt.le hta.le]
    rcases le_or_gt S.card G.card with hcard | hcard
    · -- at most `|G|` targets exceed `t`
      have h1 : ∑ i ∈ S, (x i - t) ≤ ∑ i ∈ S, (a - t) := by
        apply Finset.sum_le_sum
        intro i hi
        have := hxmax i (Finset.mem_of_mem_erase (Finset.mem_of_mem_filter i hi))
        linarith
      have h2 : ∑ j ∈ G, (a - t) ≤ ∑ j ∈ G, (y j - t) := by
        apply Finset.sum_le_sum
        intro j hj
        have := (Finset.mem_filter.1 hj).2
        linarith
      rw [Finset.sum_const, nsmul_eq_mul] at h1 h2
      have h3 : (S.card : ℝ) * (a - t) ≤ G.card * (a - t) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact_mod_cast hcard
      linarith
    · -- more than `|G|` targets exceed `t`: use the inequality at `m₂`
      have h1 := hmaj m₂
      rw [hxU, hyU] at h1
      have e1 : max (a - m₂) 0 = a - m₂ := max_eq_left (by linarith)
      have e2 : max (m₁ - m₂) 0 = m₁ - m₂ := max_eq_left (by linarith)
      have e3 : max (m₂ - m₂) 0 = 0 := by simp
      rw [e1, e2, e3, hVG m₂ le_rfl ha2] at h1
      have h2 : ∑ i ∈ S, (x i - m₂) ≤ ∑ i ∈ U.erase i₀, max (x i - m₂) 0 := by
        calc ∑ i ∈ S, (x i - m₂) ≤ ∑ i ∈ S, max (x i - m₂) 0 :=
              Finset.sum_le_sum (fun i _ => le_max_left _ _)
          _ ≤ ∑ i ∈ U.erase i₀, max (x i - m₂) 0 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun i _ _ => le_max_right _ _)
      have h3 : ∑ i ∈ S, (x i - t) = ∑ i ∈ S, (x i - m₂) - S.card * (t - m₂) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
        ring
      have h4 : ∑ j ∈ G, (y j - m₂) = ∑ j ∈ G, (y j - t) + G.card * (t - m₂) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
        ring
      have hc : (G.card : ℝ) + 1 ≤ S.card := by exact_mod_cast hcard
      have h5 : (G.card : ℝ) * (t - m₂) + (t - m₂) ≤ S.card * (t - m₂) := by
        nlinarith
      linarith

/-! ## Givens rotations and permutation matrices -/

/-- Givens rotation in the coordinate plane `(j₁, j₂)` (for `j₁ ≠ j₂`):
row `j₁` is `c e_{j₁} + s e_{j₂}`, row `j₂` is `-s e_{j₁} + c e_{j₂}`, other rows are unit. -/
def givens (j₁ j₂ : ι) (c s : ℝ) : Matrix ι ι ℝ := fun i k =>
  if i = j₁ then (if k = j₁ then c else 0) + (if k = j₂ then s else 0)
  else if i = j₂ then (if k = j₁ then -s else 0) + (if k = j₂ then c else 0)
  else if k = i then 1 else 0

/-- The action of row `i` of `givens j₁ j₂ c s` on a vector `f`. -/
def givensRow (j₁ j₂ : ι) (c s : ℝ) (i : ι) (f : ι → ℝ) : ℝ :=
  if i = j₁ then c * f j₁ + s * f j₂
  else if i = j₂ then -s * f j₁ + c * f j₂
  else f i

theorem givens_sum (j₁ j₂ : ι) (c s : ℝ) (i : ι) (f : ι → ℝ) :
    ∑ k, givens j₁ j₂ c s i k * f k = givensRow j₁ j₂ c s i f := by
  unfold givens givensRow
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib, ite_mul]

theorem givens_mem {j₁ j₂ : ι} (h12 : j₁ ≠ j₂) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    givens j₁ j₂ c s ∈ orthogonalGroup ι ℝ := by
  rw [mem_orthogonalGroup_iff]
  ext i i'
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [givens_sum]
  unfold givensRow givens
  simp only [Matrix.one_apply]
  by_cases h1 : i = j₁ <;> by_cases h2 : i = j₂ <;> by_cases h1' : i' = j₁ <;>
    by_cases h2' : i' = j₂ <;> simp_all [eq_comm] <;> nlinarith

theorem givens_conj_apply (j₁ j₂ : ι) (c s : ℝ) (M : Matrix ι ι ℝ) (u v : ι) :
    (givens j₁ j₂ c s * M * (givens j₁ j₂ c s)ᵀ) u v =
      givensRow j₁ j₂ c s v (fun k => givensRow j₁ j₂ c s u (fun l => M l k)) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply, givens_sum]
  rw [← givens_sum]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- The permutation matrix `P` with `P i j = 1` iff `σ i = j`. -/
def permMat (σ : Equiv.Perm ι) : Matrix ι ι ℝ := fun i j => if σ i = j then 1 else 0

theorem permMat_sum (σ : Equiv.Perm ι) (i : ι) (f : ι → ℝ) :
    ∑ k, permMat σ i k * f k = f (σ i) := by
  simp [permMat]

theorem permMat_mem (σ : Equiv.Perm ι) : permMat σ ∈ orthogonalGroup ι ℝ := by
  rw [mem_orthogonalGroup_iff]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [permMat_sum]
  simp [permMat, Matrix.one_apply, σ.injective.eq_iff, eq_comm]

theorem permMat_conj_apply (σ : Equiv.Perm ι) (M : Matrix ι ι ℝ) (u v : ι) :
    (permMat σ * M * (permMat σ)ᵀ) u v = M (σ u) (σ v) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply, permMat_sum]
  calc ∑ k, M (σ u) k * permMat σ v k = ∑ k, permMat σ v k * M (σ u) k :=
        Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    _ = M (σ u) (σ v) := permMat_sum σ v (fun k => M (σ u) k)

theorem permMat_conj_diagonal (σ : Equiv.Perm ι) (d : ι → ℝ) :
    permMat σ * diagonal d * (permMat σ)ᵀ = diagonal (d ∘ σ) := by
  ext u v
  rw [permMat_conj_apply]
  simp [diagonal_apply, σ.injective.eq_iff]

/-- Rotation parameters: if `m₂ ≤ a ≤ m₁` there are `c, s` with `c² + s² = 1` and
`c² m₁ + s² m₂ = a`. -/
theorem exists_rot (m₁ m₂ a : ℝ) (h2 : m₂ ≤ a) (h1 : a ≤ m₁) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c ^ 2 * m₁ + s ^ 2 * m₂ = a := by
  rcases eq_or_lt_of_le (h2.trans h1) with h | h
  · refine ⟨1, 0, by norm_num, ?_⟩
    simp only [one_pow, one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul, add_zero]
    linarith
  · have hne : m₁ - m₂ ≠ 0 := ne_of_gt (sub_pos.2 h)
    have hA : 0 ≤ (a - m₂) / (m₁ - m₂) := div_nonneg (by linarith) (by linarith)
    have hB : 0 ≤ (m₁ - a) / (m₁ - m₂) := div_nonneg (by linarith) (by linarith)
    refine ⟨Real.sqrt ((a - m₂) / (m₁ - m₂)), Real.sqrt ((m₁ - a) / (m₁ - m₂)), ?_, ?_⟩
    · rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
      field_simp
      ring
    · rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
      field_simp
      ring

/-! ## The induction -/

/-- Inductive form of Schur–Horn. `M` is diagonal on the set `U` of unfinished indices and the
targets `x` on `U` are majorized by the diagonal of `M` on `U`. Then some orthogonal `G` puts the
targets on the diagonal at `U` and does not change the diagonal outside `U`. -/
theorem schurHorn_aux (N : ℕ) : ∀ (U : Finset ι) (M : Matrix ι ι ℝ) (x : ι → ℝ),
    U.card = N → (∀ u ∈ U, ∀ v ∈ U, u ≠ v → M u v = 0) → MajOn U x (fun i => M i i) →
    ∃ G ∈ orthogonalGroup ι ℝ, (∀ i ∈ U, (G * M * Gᵀ) i i = x i) ∧
      (∀ i ∉ U, (G * M * Gᵀ) i i = M i i) := by
  induction N with
  | zero =>
    intro U M x hU _ _
    rw [Finset.card_eq_zero] at hU
    subst hU
    exact ⟨1, one_mem _, fun i hi => absurd hi (Finset.notMem_empty i), fun i _ => by simp⟩
  | succ N ih =>
    intro U M x hU hdiag hmaj
    have hne : U.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨i₀, hi₀, hxmax⟩ := U.exists_max_image x hne
    obtain ⟨j₁, hj₁, hMmax⟩ := U.exists_max_image (fun i => M i i) hne
    have ha1 : x i₀ ≤ M j₁ j₁ := by
      have h := hmaj.2 (M j₁ j₁)
      have h0 : ∑ i ∈ U, max (M i i - M j₁ j₁) 0 = 0 :=
        Finset.sum_eq_zero fun i hi => max_eq_right (by linarith [hMmax i hi])
      rw [h0] at h
      have h1 : max (x i₀ - M j₁ j₁) 0 ≤ ∑ i ∈ U, max (x i - M j₁ j₁) 0 :=
        Finset.single_le_sum (f := fun i => max (x i - M j₁ j₁) 0)
          (fun i _ => le_max_right _ _) hi₀
      linarith [le_max_left (x i₀ - M j₁ j₁) 0]
    by_cases hex : ∃ j ∈ U, j ≠ j₁ ∧ M j j ≤ x i₀
    · -- main case: a genuine rotation
      obtain ⟨j₂, hj₂U2, hmax2⟩ :=
        ((U.erase j₁).filter (fun j => M j j ≤ x i₀)).exists_max_image (fun j => M j j) (by
          obtain ⟨j, hj, hj1, hjle⟩ := hex
          exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hj1, hj⟩, hjle⟩⟩)
      obtain ⟨hj₂e, ha2⟩ := Finset.mem_filter.1 hj₂U2
      have h21 : j₂ ≠ j₁ := Finset.ne_of_mem_erase hj₂e
      have h12 : j₁ ≠ j₂ := h21.symm
      have hj₂ : j₂ ∈ U := Finset.mem_of_mem_erase hj₂e
      have hgap : ∀ j ∈ U, j ≠ j₁ → j ≠ j₂ → M j j ≤ M j₂ j₂ ∨ x i₀ ≤ M j j := by
        intro j hj hj1 _
        by_cases hjle : M j j ≤ x i₀
        · exact Or.inl (hmax2 j (Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hj1, hj⟩, hjle⟩))
        · exact Or.inr (le_of_not_ge hjle)
      obtain ⟨c, s, hcs, hcsa⟩ := exists_rot (M j₁ j₁) (M j₂ j₂) (x i₀) ha2 ha1
      set G₁ := givens j₁ j₂ c s with hG₁
      set M' := G₁ * M * G₁ᵀ with hM'def
      set τ := Equiv.swap i₀ j₁ with hτ
      set M'' := permMat τ * M' * (permMat τ)ᵀ with hM''def
      have hM''app : ∀ u v, M'' u v = M' (τ u) (τ v) := fun u v => permMat_conj_apply τ M' u v
      have hM'app : ∀ u v, M' u v = givensRow j₁ j₂ c s v
          (fun k => givensRow j₁ j₂ c s u (fun l => M l k)) :=
        fun u v => givens_conj_apply j₁ j₂ c s M u v
      have hM12 : M j₁ j₂ = 0 := hdiag j₁ hj₁ j₂ hj₂ h12
      have hM21 : M j₂ j₁ = 0 := hdiag j₂ hj₂ j₁ hj₁ h21
      -- the rotated matrix `M'`
      have F1 : M' j₁ j₁ = x i₀ := by
        rw [hM'app]
        simp only [givensRow, if_true, hM12, hM21]
        linear_combination hcsa
      have F2 : M' j₂ j₂ = M j₁ j₁ + M j₂ j₂ - x i₀ := by
        rw [hM'app]
        simp only [givensRow, if_true, if_neg h21, hM12, hM21]
        linear_combination (M j₁ j₁ + M j₂ j₂) * hcs - hcsa
      have F3 : ∀ u, u ≠ j₁ → u ≠ j₂ → M' u u = M u u := by
        intro u hu1 hu2
        rw [hM'app]
        simp only [givensRow, if_neg hu1, if_neg hu2]
      have F4 : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → u ≠ j₁ → v ≠ j₁ → M' u v = 0 := by
        intro u hu v hv huv hu1 hv1
        rw [hM'app]
        by_cases hu2 : u = j₂
        · have hv2 : v ≠ j₂ := fun h => huv (hu2.trans h.symm)
          have z1 : M j₁ v = 0 := hdiag j₁ hj₁ v hv (Ne.symm hv1)
          have z2 : M j₂ v = 0 := hdiag j₂ hj₂ v hv (fun h => hv2 h.symm)
          simp only [givensRow, if_neg hv1, if_neg hv2, hu2, if_neg h21, if_true, z1, z2]
          ring
        · by_cases hv2 : v = j₂
          · have z1 : M u j₁ = 0 := hdiag u hu j₁ hj₁ hu1
            have z2 : M u j₂ = 0 := hdiag u hu j₂ hj₂ hu2
            simp only [givensRow, hv2, if_neg h21, if_true, if_neg hu1, if_neg hu2, z1, z2]
            ring
          · simp only [givensRow, if_neg hu1, if_neg hu2, if_neg hv1, if_neg hv2]
            exact hdiag u hu v hv huv
      -- the swap `τ`
      have hτU : ∀ i ∈ U, τ i ∈ U := by
        intro i hi
        rw [hτ, Equiv.swap_apply_def]
        split_ifs
        · exact hj₁
        · exact hi₀
        · exact hi
      have hτ1 : ∀ i, i ≠ i₀ → τ i ≠ j₁ := by
        intro i hi h
        apply hi
        have := congrArg τ h
        rwa [hτ, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      have hτ0 : ∀ j, j ≠ j₁ → τ j ≠ i₀ := by
        intro j hj h
        apply hj
        have := congrArg τ h
        rwa [hτ, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have hτout : ∀ i ∉ U, τ i = i := by
        intro i hi
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ hi₀)) (fun h => hi (h ▸ hj₁))
      have hsum_swap : ∀ f : ι → ℝ, ∑ i ∈ U.erase i₀, f (τ i) = ∑ j ∈ U.erase j₁, f j := by
        intro f
        apply Finset.sum_nbij' (fun i => τ i) (fun j => τ j)
        · intro i hi
          exact Finset.mem_erase.2
            ⟨hτ1 i (Finset.ne_of_mem_erase hi), hτU i (Finset.mem_of_mem_erase hi)⟩
        · intro j hj
          exact Finset.mem_erase.2
            ⟨hτ0 j (Finset.ne_of_mem_erase hj), hτU j (Finset.mem_of_mem_erase hj)⟩
        · intro i _
          exact Equiv.swap_apply_self _ _ _
        · intro j _
          exact Equiv.swap_apply_self _ _ _
        · intro i _
          rfl
      have hsplit : ∀ f : ι → ℝ, ∑ j ∈ U.erase j₁, f j =
          f j₂ + ∑ j ∈ (U.erase j₁).erase j₂, f j :=
        fun f => (Finset.add_sum_erase _ f hj₂e).symm
      have hV' : ∀ j ∈ (U.erase j₁).erase j₂, M' j j = M j j := fun j hj =>
        F3 j (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
      -- the inductive hypotheses for `U.erase i₀` and `M''`
      have hdiag'' : ∀ u ∈ U.erase i₀, ∀ v ∈ U.erase i₀, u ≠ v → M'' u v = 0 := by
        intro u hu v hv huv
        rw [hM''app]
        exact F4 (τ u) (hτU u (Finset.mem_of_mem_erase hu)) (τ v)
          (hτU v (Finset.mem_of_mem_erase hv)) (τ.injective.ne huv)
          (hτ1 u (Finset.ne_of_mem_erase hu)) (hτ1 v (Finset.ne_of_mem_erase hv))
      have hmaj'' : MajOn (U.erase i₀) x (fun i => M'' i i) := by
        constructor
        · have e1 : ∑ i ∈ U.erase i₀, M'' i i = ∑ j ∈ U.erase j₁, M' j j := by
            simp only [hM''app]
            exact hsum_swap (fun j => M' j j)
          show ∑ i ∈ U.erase i₀, x i = ∑ i ∈ U.erase i₀, M'' i i
          rw [e1, hsplit, F2, Finset.sum_congr rfl hV']
          have h := hmaj.1
          simp only at h
          rw [← Finset.add_sum_erase U x hi₀, ← Finset.add_sum_erase U _ hj₁,
            ← Finset.add_sum_erase _ _ hj₂e] at h
          linarith
        · intro t
          have h := maj_step U x (fun i => M i i) i₀ j₁ j₂ hi₀ hj₁ hj₂ h12 hxmax ha1 ha2 hgap
            hmaj.2 t
          have e1 : ∑ i ∈ U.erase i₀, max (M'' i i - t) 0 =
              ∑ j ∈ U.erase j₁, max (M' j j - t) 0 := by
            simp only [hM''app]
            exact hsum_swap (fun j => max (M' j j - t) 0)
          show ∑ i ∈ U.erase i₀, max (x i - t) 0 ≤ ∑ i ∈ U.erase i₀, max (M'' i i - t) 0
          rw [e1, hsplit, F2, add_comm]
          have e2 : ∑ j ∈ (U.erase j₁).erase j₂, max (M' j j - t) 0 =
              ∑ j ∈ (U.erase j₁).erase j₂, max (M j j - t) 0 :=
            Finset.sum_congr rfl (fun j hj => by rw [hV' j hj])
          rw [e2]
          exact h
      obtain ⟨G', hG', hin, hout⟩ := ih (U.erase i₀) M'' x
        (by rw [Finset.card_erase_of_mem hi₀, hU]; rfl) hdiag'' hmaj''
      have hconj : G' * permMat τ * G₁ * M * (G' * permMat τ * G₁)ᵀ = G' * M'' * G'ᵀ := by
        simp only [hM''def, hM'def, Matrix.transpose_mul, Matrix.mul_assoc]
      refine ⟨G' * permMat τ * G₁,
        mul_mem (mul_mem hG' (permMat_mem τ)) (givens_mem h12 hcs), ?_, ?_⟩
      · intro i hi
        rw [hconj]
        by_cases hii : i = i₀
        · rw [hii, hout i₀ (Finset.notMem_erase i₀ U), hM''app, hτ, Equiv.swap_apply_left]
          exact F1
        · exact hin i (Finset.mem_erase.2 ⟨hii, hi⟩)
      · intro i hi
        rw [hconj, hout i (fun h => hi (Finset.mem_of_mem_erase h)), hM''app, hτout i hi]
        exact F3 i (fun h => hi (h ▸ hj₁)) (fun h => hi (h ▸ hj₂))
    · -- degenerate case: `U = {j₁}`
      push Not at hex
      have hU1 : ∀ j ∈ U, j = j₁ := by
        by_contra hcon
        push Not at hcon
        obtain ⟨j, hj, hjne⟩ := hcon
        have hlt : ∑ i ∈ U, x i < ∑ i ∈ U, M i i := by
          apply Finset.sum_lt_sum
          · intro i hi
            by_cases h : i = j₁
            · rw [h]
              exact (hxmax j₁ hj₁).trans ha1
            · exact (hxmax i hi).trans (hex i hi h).le
          · exact ⟨j, hj, (hxmax j hj).trans_lt (hex j hj hjne)⟩
        exact absurd hmaj.1 (ne_of_lt hlt)
      have hUeq : U = {j₁} := by
        ext j
        simp only [Finset.mem_singleton]
        exact ⟨hU1 j, fun h => h ▸ hj₁⟩
      refine ⟨1, one_mem _, ?_, ?_⟩
      · intro i hi
        have hi' : i = j₁ := hU1 i hi
        have h := hmaj.1
        rw [hUeq, Finset.sum_singleton, Finset.sum_singleton] at h
        simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one, hi']
        exact h.symm
      · intro i _
        simp

/-- **Real Schur–Horn theorem** (existence direction). If `x ≺ λ`, there is a real orthogonal
matrix `G` such that the diagonal of `G * diagonal λ * Gᵀ` is `x`. -/
theorem schurHorn (lam x : ι → ℝ) (h : MajOn Finset.univ x lam) :
    ∃ G ∈ orthogonalGroup ι ℝ, ∀ i, (G * diagonal lam * Gᵀ) i i = x i := by
  obtain ⟨G, hG, hin, -⟩ := schurHorn_aux _ Finset.univ (diagonal lam) x rfl
    (fun u _ v _ huv => diagonal_apply_ne _ huv) (by simpa [MajOn] using h)
  exact ⟨G, hG, fun i => hin i (Finset.mem_univ i)⟩

end STUProof
