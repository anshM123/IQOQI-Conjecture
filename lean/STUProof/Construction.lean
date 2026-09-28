import STUProof.SchurHorn

/-!
# Step 1: every `v_k(p)` is a symmetric marginal of `p ⊗ p`

Let `p ∈ ℝ^d` be a probability vector sorted in decreasing order and `0 ≤ k < d`. Put `n = k + 1`,
`P = p_0 + … + p_k` and `v_k = (P/n, …, P/n, p_{k+1}, …, p_{d-1})`. We construct an explicit
real orthogonal matrix `O` on `ℝ^d ⊗ ℝ^d` such that both partial traces of
`O · diag(p ⊗ p) · Oᵀ` are equal to `diag(v_k)` (`vk_reachable`).

## Construction

Write the local index set as `T ⊕ J` with `T = Fin n` (cyclic group) and `J` the tails;
`π = p|_T`, `q = p|_J`.

1. Tail relabelling: every tail `j` gets a shift `r_j ∈ T`; the basis vectors `|a, j⟩` and
   `|j, a⟩` are moved to `|a + r_j, j⟩` and `|j, a + r_j⟩`. The shifts come from a greedy
   bin-packing argument, so that each bin weight `W_c = ∑_{r_j = c} q_j` is at most `1/n`
   (`exists_binPacking`).
2. Put `β_c = (1/n - W_c)/P ≥ 0`; then `∑ β_c = 1`. On each cyclic diagonal
   `D_s = {|a, a + s⟩ : a ∈ T}` of `T × T` we apply an orthogonal matrix (real Schur–Horn,
   `schurHorn`) that turns `diag(λ^s)`, `λ^s_a = π_a π_{a+s}`, into a matrix with diagonal
   `x^s_a = ∑_c β_c λ^s_{a-c}` (`x^s ≺ λ^s`, `majOn_circulant`).
3. Bookkeeping: the cyclic diagonals have distinct rows and distinct columns, so both marginals
   stay diagonal; row `a ∈ T` receives `∑_c (P β_c + W_c) π_{a-c} = P/n`, and tail rows and
   columns keep `p_j`.
-/

open Matrix Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace STUProof

/-! ## Partial traces and the target vectors -/

/-- Partial trace over the second tensor factor: `(Tr_B ρ)_{a a'} = ∑_b ρ_{(a,b),(a',b)}`. -/
def partialTraceB {m n R : Type*} [Fintype n] [AddCommMonoid R]
    (ρ : Matrix (m × n) (m × n) R) : Matrix m m R :=
  Matrix.of fun a a' => ∑ b, ρ (a, b) (a', b)

/-- Partial trace over the first tensor factor: `(Tr_A ρ)_{b b'} = ∑_a ρ_{(a,b),(a,b')}`. -/
def partialTraceA {m n R : Type*} [Fintype m] [AddCommMonoid R]
    (ρ : Matrix (m × n) (m × n) R) : Matrix n n R :=
  Matrix.of fun b b' => ∑ a, ρ (a, b) (a, b')

/-- The vector `v_k(p)`: the entries `p_0, …, p_k` are replaced by their mean. -/
def vk {d : ℕ} (p : Fin d → ℝ) (k : Fin d) : Fin d → ℝ :=
  fun i => if i ≤ k then (∑ j with j ≤ k, p j) / ((k : ℕ) + 1 : ℝ) else p i

/-! ## General facts on orthogonal matrices -/

section General

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem submatrix_mem_orthogonalGroup {G : Matrix ι ι ℝ} (hG : G ∈ orthogonalGroup ι ℝ)
    (e : κ ≃ ι) : G.submatrix e e ∈ orthogonalGroup κ ℝ := by
  rw [mem_orthogonalGroup_iff] at hG ⊢
  rw [transpose_submatrix, submatrix_mul_equiv, hG, submatrix_one_equiv]

theorem conj_submatrix (G D : Matrix ι ι ℝ) (e : κ ≃ ι) :
    G.submatrix e e * D.submatrix e e * (G.submatrix e e)ᵀ = (G * D * Gᵀ).submatrix e e := by
  rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

theorem fromBlocks_mem_orthogonalGroup {A : Matrix ι ι ℝ} {D : Matrix κ κ ℝ}
    (hA : A ∈ orthogonalGroup ι ℝ) (hD : D ∈ orthogonalGroup κ ℝ) :
    fromBlocks A 0 0 D ∈ orthogonalGroup (ι ⊕ κ) ℝ := by
  rw [mem_orthogonalGroup_iff] at hA hD ⊢
  rw [fromBlocks_transpose, fromBlocks_multiply]
  simp [hA, hD]

theorem fromBlocks_conj (A E : Matrix ι ι ℝ) (D F : Matrix κ κ ℝ) :
    fromBlocks A 0 0 D * fromBlocks E 0 0 F * (fromBlocks A 0 0 D)ᵀ =
      fromBlocks (A * E * Aᵀ) 0 0 (D * F * Dᵀ) := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

omit [Fintype ι] in
theorem blockDiagonal_mem_orthogonalGroup {W : κ → Matrix ι ι ℝ} [Fintype ι]
    (hW : ∀ k, W k ∈ orthogonalGroup ι ℝ) : blockDiagonal W ∈ orthogonalGroup (ι × κ) ℝ := by
  rw [mem_orthogonalGroup_iff]
  rw [blockDiagonal_transpose, ← blockDiagonal_mul]
  have : (fun k => W k * (W k)ᵀ) = (1 : κ → Matrix ι ι ℝ) := by
    funext k
    exact (mem_orthogonalGroup_iff _ _).1 (hW k)
  rw [this, blockDiagonal_one]

theorem blockDiagonal_conj (W V : κ → Matrix ι ι ℝ) :
    blockDiagonal W * blockDiagonal V * (blockDiagonal W)ᵀ =
      blockDiagonal fun k => W k * V k * (W k)ᵀ := by
  rw [blockDiagonal_transpose, ← blockDiagonal_mul, ← blockDiagonal_mul]

end General

/-! ## The sector decomposition -/

section Construction

variable {n : ℕ} [NeZero n] {J : Type*} [Fintype J] [DecidableEq J]

/-- The four sectors of `(T ⊕ J) × (T ⊕ J)`: `T × T`, `T × J`, `J × T` (stored as `T × J`) and
`J × J`. -/
def sectorEquiv : (Fin n ⊕ J) × (Fin n ⊕ J) ≃
    (Fin n × Fin n) ⊕ ((Fin n × J) ⊕ ((Fin n × J) ⊕ (J × J))) where
  toFun
    | (Sum.inl a, Sum.inl b) => Sum.inl (a, b)
    | (Sum.inl a, Sum.inr j) => Sum.inr (Sum.inl (a, j))
    | (Sum.inr j, Sum.inl a) => Sum.inr (Sum.inr (Sum.inl (a, j)))
    | (Sum.inr j, Sum.inr l) => Sum.inr (Sum.inr (Sum.inr (j, l)))
  invFun
    | Sum.inl (a, b) => (Sum.inl a, Sum.inl b)
    | Sum.inr (Sum.inl (a, j)) => (Sum.inl a, Sum.inr j)
    | Sum.inr (Sum.inr (Sum.inl (a, j))) => (Sum.inr j, Sum.inl a)
    | Sum.inr (Sum.inr (Sum.inr (j, l))) => (Sum.inr j, Sum.inr l)
  left_inv := by rintro ⟨a | a, b | b⟩ <;> rfl
  right_inv := by rintro (⟨a, b⟩ | ⟨a, j⟩ | ⟨a, j⟩ | ⟨j, l⟩) <;> rfl

@[simp] theorem sectorEquiv_inl_inl (a b : Fin n) :
    (sectorEquiv (J := J) (Sum.inl a, Sum.inl b)) = Sum.inl (a, b) := rfl
@[simp] theorem sectorEquiv_inl_inr (a : Fin n) (j : J) :
    (sectorEquiv (Sum.inl a, Sum.inr j)) = Sum.inr (Sum.inl (a, j)) := rfl
@[simp] theorem sectorEquiv_inr_inl (j : J) (a : Fin n) :
    (sectorEquiv (Sum.inr j, Sum.inl a)) = Sum.inr (Sum.inr (Sum.inl (a, j))) := rfl
@[simp] theorem sectorEquiv_inr_inr (j l : J) :
    (sectorEquiv (n := n) (Sum.inr j, Sum.inr l)) = Sum.inr (Sum.inr (Sum.inr (j, l))) := rfl

/-- The change of coordinates `(a, b) ↦ (a, b - a)` on `T × T`: the second coordinate becomes the
label `s` of the cyclic diagonal `D_s = {(a, a + s)}`. -/
def diagEquiv : Fin n × Fin n ≃ Fin n × Fin n where
  toFun x := (x.1, x.2 - x.1)
  invFun y := (y.1, y.1 + y.2)
  left_inv x := by simp
  right_inv y := by simp

@[simp] theorem diagEquiv_apply (x : Fin n × Fin n) : diagEquiv x = (x.1, x.2 - x.1) := rfl
@[simp] theorem diagEquiv_symm_apply (y : Fin n × Fin n) :
    diagEquiv.symm y = (y.1, y.1 + y.2) := rfl

/-- The orthogonal matrix of the construction, in sector coordinates. `W s` acts on the cyclic
diagonal `D_s`; `r j` is the shift of tail `j`. -/
def sectorMat (W : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : J → Fin n) :
    Matrix ((Fin n × Fin n) ⊕ ((Fin n × J) ⊕ ((Fin n × J) ⊕ (J × J))))
      ((Fin n × Fin n) ⊕ ((Fin n × J) ⊕ ((Fin n × J) ⊕ (J × J)))) ℝ :=
  fromBlocks ((blockDiagonal W).submatrix diagEquiv diagEquiv) 0 0
    (fromBlocks (blockDiagonal fun j => permMat (Equiv.subRight (r j))) 0 0
      (fromBlocks (blockDiagonal fun j => permMat (Equiv.subRight (r j))) 0 0 1))

/-- The orthogonal matrix of the construction on `(T ⊕ J) × (T ⊕ J)`. -/
def constrMat (W : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : J → Fin n) :
    Matrix ((Fin n ⊕ J) × (Fin n ⊕ J)) ((Fin n ⊕ J) × (Fin n ⊕ J)) ℝ :=
  (sectorMat W r).submatrix sectorEquiv sectorEquiv

theorem constrMat_mem {W : Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ s, W s ∈ orthogonalGroup (Fin n) ℝ) (r : J → Fin n) :
    constrMat W r ∈ orthogonalGroup ((Fin n ⊕ J) × (Fin n ⊕ J)) ℝ := by
  unfold constrMat sectorMat
  apply submatrix_mem_orthogonalGroup
  have hP : blockDiagonal (fun j => permMat (Equiv.subRight (r j))) ∈
      orthogonalGroup (Fin n × J) ℝ :=
    blockDiagonal_mem_orthogonalGroup (fun j => permMat_mem _)
  refine fromBlocks_mem_orthogonalGroup
    (submatrix_mem_orthogonalGroup (blockDiagonal_mem_orthogonalGroup hW) _)
    (fromBlocks_mem_orthogonalGroup hP (fromBlocks_mem_orthogonalGroup hP (one_mem _)))

/-- The weights `λ^s_a = π_a π_{a+s}` on the cyclic diagonal `D_s`. -/
def lamS (π : Fin n → ℝ) (s : Fin n) : Fin n → ℝ := fun a => π a * π (a + s)

/-- The state produced by the construction, in sector coordinates. -/
def sectorState (W : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : J → Fin n) (π : Fin n → ℝ)
    (q : J → ℝ) :
    Matrix ((Fin n × Fin n) ⊕ ((Fin n × J) ⊕ ((Fin n × J) ⊕ (J × J))))
      ((Fin n × Fin n) ⊕ ((Fin n × J) ⊕ ((Fin n × J) ⊕ (J × J)))) ℝ :=
  fromBlocks ((blockDiagonal fun s => W s * diagonal (lamS π s) * (W s)ᵀ).submatrix
      diagEquiv diagEquiv) 0 0
    (fromBlocks (diagonal fun x => π (x.1 - r x.2) * q x.2) 0 0
      (fromBlocks (diagonal fun x => q x.2 * π (x.1 - r x.2)) 0 0
        (diagonal fun x => q x.1 * q x.2)))

theorem permMat_subRight_conj (c : Fin n) (u : Fin n → ℝ) :
    permMat (Equiv.subRight c) * diagonal u * (permMat (Equiv.subRight c))ᵀ =
      diagonal fun a => u (a - c) := by
  rw [permMat_conj_diagonal]
  rfl

theorem constrMat_conj (W : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : J → Fin n)
    (π : Fin n → ℝ) (q : J → ℝ) :
    constrMat W r * diagonal (fun x => Sum.elim π q x.1 * Sum.elim π q x.2) *
        (constrMat W r)ᵀ = (sectorState W r π q).submatrix sectorEquiv sectorEquiv := by
  have hD : diagonal (fun x : (Fin n ⊕ J) × (Fin n ⊕ J) => Sum.elim π q x.1 * Sum.elim π q x.2) =
      (fromBlocks (diagonal fun x : Fin n × Fin n => π x.1 * π x.2) 0 0
        (fromBlocks (diagonal fun x : Fin n × J => π x.1 * q x.2) 0 0
          (fromBlocks (diagonal fun x : Fin n × J => q x.2 * π x.1) 0 0
            (diagonal fun x : J × J => q x.1 * q x.2)))).submatrix sectorEquiv sectorEquiv := by
    simp only [fromBlocks_diagonal, submatrix_diagonal_equiv]
    congr 1
    funext x
    rcases x with ⟨a | a, b | b⟩ <;> rfl
  rw [hD, constrMat, conj_submatrix]
  congr 1
  unfold sectorMat sectorState
  rw [fromBlocks_conj, fromBlocks_conj, fromBlocks_conj]
  congr 1
  · -- the `T × T` sector
    have h1 : diagonal (fun x : Fin n × Fin n => π x.1 * π x.2) =
        (blockDiagonal fun s => diagonal (lamS π s)).submatrix diagEquiv diagEquiv := by
      rw [blockDiagonal_diagonal, submatrix_diagonal_equiv]
      congr 1
      funext x
      simp [lamS]
    rw [h1, conj_submatrix, blockDiagonal_conj]
  · congr 1
    · rw [← blockDiagonal_diagonal (d := fun j a => π a * q j), blockDiagonal_conj]
      simp only [permMat_subRight_conj, blockDiagonal_diagonal]
    · congr 1
      · rw [← blockDiagonal_diagonal (d := fun j a => q j * π a), blockDiagonal_conj]
        simp only [permMat_subRight_conj, blockDiagonal_diagonal]
      · simp

/-! ## The marginals of the constructed state -/

theorem partialTraceB_sectorState (W : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : J → Fin n)
    (π : Fin n → ℝ) (q : J → ℝ) :
    partialTraceB ((sectorState W r π q).submatrix sectorEquiv sectorEquiv) =
      diagonal (Sum.elim
        (fun a => ∑ b, (W (b - a) * diagonal (lamS π (b - a)) * (W (b - a))ᵀ) a a +
          ∑ j, π (a - r j) * q j)
        (fun j => ∑ b, q j * π (b - r j) + ∑ l, q j * q l)) := by
  ext u u'
  simp only [partialTraceB, Matrix.of_apply, Matrix.submatrix_apply, Fintype.sum_sum_type]
  rcases u with a | j <;> rcases u' with a' | j'
  · simp only [sectorEquiv_inl_inl, sectorEquiv_inl_inr, sectorState, fromBlocks_apply₁₁,
      fromBlocks_apply₂₂, submatrix_apply, diagEquiv_apply, blockDiagonal_apply', diagonal_apply,
      Sum.inl.injEq, Prod.mk.injEq, and_true, sub_right_inj, Sum.elim_inl]
    by_cases h : a = a'
    · subst h
      simp
    · simp [h]
  · simp [sectorState]
  · simp [sectorState]
  · simp only [sectorEquiv_inr_inl, sectorEquiv_inr_inr, sectorState, fromBlocks_apply₂₂,
      fromBlocks_apply₁₁, diagonal_apply, Sum.inr.injEq, Prod.mk.injEq, true_and, and_true,
      Sum.elim_inr]
    by_cases h : j = j'
    · subst h
      simp
    · simp [h]

theorem partialTraceA_sectorState (W : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : J → Fin n)
    (π : Fin n → ℝ) (q : J → ℝ) :
    partialTraceA ((sectorState W r π q).submatrix sectorEquiv sectorEquiv) =
      diagonal (Sum.elim
        (fun b => ∑ a, (W (b - a) * diagonal (lamS π (b - a)) * (W (b - a))ᵀ) a a +
          ∑ j, q j * π (b - r j))
        (fun j => ∑ a, π (a - r j) * q j + ∑ l, q l * q j)) := by
  ext u u'
  simp only [partialTraceA, Matrix.of_apply, Matrix.submatrix_apply, Fintype.sum_sum_type]
  rcases u with b | j <;> rcases u' with b' | j'
  · simp only [sectorEquiv_inl_inl, sectorEquiv_inr_inl, sectorState, fromBlocks_apply₁₁,
      fromBlocks_apply₂₂, submatrix_apply, diagEquiv_apply, blockDiagonal_apply', diagonal_apply,
      Sum.inl.injEq, Prod.mk.injEq, and_true, sub_left_inj, Sum.elim_inl]
    by_cases h : b = b'
    · subst h
      simp
    · simp [h]
  · simp [sectorState]
  · simp [sectorState]
  · simp only [sectorEquiv_inl_inr, sectorEquiv_inr_inr, sectorState, fromBlocks_apply₂₂,
      fromBlocks_apply₁₁, diagonal_apply, Sum.inr.injEq, Prod.mk.injEq, true_and, Sum.elim_inr]
    by_cases h : j = j'
    · subst h
      simp
    · simp [h]

/-! ## Circulant mixing, bin packing, and the marginal bookkeeping -/

/-- A circulant doubly stochastic matrix `B = ∑_c β_c Π^c` maps `λ` to a vector majorized by
`λ` (Jensen for `t ↦ (t - s)⁺`). -/
theorem majOn_circulant (β lam : Fin n → ℝ) (hβ0 : ∀ c, 0 ≤ β c) (hβ1 : ∑ c, β c = 1) :
    MajOn Finset.univ (fun a => ∑ c, β c * lam (a - c)) lam := by
  have hshift : ∀ (f : Fin n → ℝ) (c : Fin n), ∑ a, f (a - c) = ∑ a, f a :=
    fun f c => Equiv.sum_comp (Equiv.subRight c) f
  constructor
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hshift lam]
    rw [← Finset.sum_mul, hβ1, one_mul]
  · intro t
    have key : ∀ a, max (∑ c, β c * lam (a - c) - t) 0 ≤ ∑ c, β c * max (lam (a - c) - t) 0 := by
      intro a
      apply max_le
      · have e : ∑ c, β c * lam (a - c) - t = ∑ c, β c * (lam (a - c) - t) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hβ1, one_mul]
        rw [e]
        exact Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hβ0 c))
      · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hβ0 c) (le_max_right _ _))
    calc ∑ a, max (∑ c, β c * lam (a - c) - t) 0
        ≤ ∑ a, ∑ c, β c * max (lam (a - c) - t) 0 := Finset.sum_le_sum (fun a _ => key a)
      _ = ∑ c, β c * ∑ a, max (lam (a - c) - t) 0 := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ = ∑ c, β c * ∑ a, max (lam a - t) 0 := by
          simp_rw [hshift (fun a => max (lam a - t) 0)]
      _ = ∑ a, max (lam a - t) 0 := by rw [← Finset.sum_mul, hβ1, one_mul]

/-- Greedy bin packing: if every item satisfies `(n - 1) q_j + ∑ q ≤ 1`, the items can be put
into `n` bins of capacity `1/n`. (Put each item into the currently lightest bin.) -/
theorem exists_binPacking (q : J → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hbound : ∀ j, ((n : ℝ) - 1) * q j + ∑ j, q j ≤ 1) :
    ∃ r : J → Fin n, ∀ c, ∑ j with r j = c, q j ≤ 1 / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  suffices h : ∀ S : Finset J, ∃ r : J → Fin n, ∀ c, ∑ j ∈ S with r j = c, q j ≤ 1 / n from
    h Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun c => ?_⟩
    simp only [Finset.filter_empty, Finset.sum_empty]
    positivity
  | insert a S ha ih =>
    obtain ⟨r, hr⟩ := ih
    set Wc : Fin n → ℝ := fun c => ∑ j ∈ S with r j = c, q j with hWc
    obtain ⟨c₀, -, hc₀⟩ := Finset.univ.exists_min_image Wc Finset.univ_nonempty
    refine ⟨Function.update r a c₀, fun c => ?_⟩
    have hsplit : ∑ j ∈ insert a S with Function.update r a c₀ j = c, q j =
        (if c₀ = c then q a else 0) + Wc c := by
      rw [Finset.sum_filter, Finset.sum_insert ha, Function.update_self]
      congr 1
      simp only [hWc]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj ha)]
    rw [hsplit]
    by_cases hc : c₀ = c
    · rw [if_pos hc, ← hc]
      have h1 : (n : ℝ) * Wc c₀ ≤ ∑ c, Wc c := by
        have : ∑ _c : Fin n, Wc c₀ ≤ ∑ c, Wc c :=
          Finset.sum_le_sum (fun c _ => hc₀ c (Finset.mem_univ c))
        simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
      have h2 : ∑ c, Wc c = ∑ j ∈ S, q j := Finset.sum_fiberwise S r q
      have h3 : q a + ∑ j ∈ S, q j ≤ ∑ j, q j := by
        rw [← Finset.sum_insert ha]
        exact Finset.sum_le_univ_sum_of_nonneg hq
      have h4 := hbound a
      rw [le_div_iff₀ hn]
      nlinarith
    · rw [if_neg hc, zero_add]
      exact hr c

theorem sum_sub_eq (f : Fin n → ℝ) (c : Fin n) : ∑ a, f (a - c) = ∑ a, f a :=
  Equiv.sum_comp (Equiv.subRight c) f

theorem sum_sub_left_eq (f : Fin n → ℝ) (a : Fin n) : ∑ c, f (a - c) = ∑ c, f c :=
  Equiv.sum_comp (Equiv.subLeft a) f

/-- Row `a ∈ T` of the reduced state of A. -/
theorem row_T (π : Fin n → ℝ) (q : J → ℝ) (r : J → Fin n) (β : Fin n → ℝ) (a : Fin n)
    (hβW : ∀ c, (∑ b, π b) * β c + ∑ j with r j = c, q j = 1 / n) :
    ∑ b, ∑ c, β c * lamS π (b - a) (a - c) + ∑ j, π (a - r j) * q j = (∑ b, π b) / n := by
  have e1 : ∑ b, ∑ c, β c * lamS π (b - a) (a - c) =
      ∑ c, π (a - c) * ((∑ b, π b) * β c) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    have h : ∀ b, a - c + (b - a) = b - c := fun b => by abel
    simp only [lamS, h]
    rw [← sum_sub_eq π c, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have e2 : ∑ j, π (a - r j) * q j = ∑ c, π (a - c) * ∑ j with r j = c, q j := by
    rw [← Finset.sum_fiberwise Finset.univ r (fun j => π (a - r j) * q j)]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.1 hj).2]
  rw [e1, e2, ← Finset.sum_add_distrib]
  simp_rw [← mul_add, hβW]
  rw [← Finset.sum_mul, sum_sub_left_eq π a, mul_one_div]

/-- Column `b ∈ T` of the reduced state of B. -/
theorem col_T (π : Fin n → ℝ) (q : J → ℝ) (r : J → Fin n) (β : Fin n → ℝ) (b : Fin n)
    (hβW : ∀ c, (∑ b, π b) * β c + ∑ j with r j = c, q j = 1 / n) :
    ∑ a, ∑ c, β c * lamS π (b - a) (a - c) + ∑ j, q j * π (b - r j) = (∑ b, π b) / n := by
  have e1 : ∑ a, ∑ c, β c * lamS π (b - a) (a - c) =
      ∑ c, π (b - c) * ((∑ b, π b) * β c) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    have h : ∀ a, a - c + (b - a) = b - c := fun a => by abel
    simp only [lamS, h]
    rw [← sum_sub_eq π c, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have e2 : ∑ j, q j * π (b - r j) = ∑ c, π (b - c) * ∑ j with r j = c, q j := by
    rw [← Finset.sum_fiberwise Finset.univ r (fun j => q j * π (b - r j))]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.1 hj).2, mul_comm]
  rw [e1, e2, ← Finset.sum_add_distrib]
  simp_rw [← mul_add, hβW]
  rw [← Finset.sum_mul, sum_sub_left_eq π b, mul_one_div]

/-- **Step 1 on `(T ⊕ J) × (T ⊕ J)`.** For weights `π` on `T = Fin n` and `q` on the tails `J`
with `q_j ≤ π_a` for all `j, a` and total mass `1`, some real orthogonal `O` makes both marginals
of `O diag(p ⊗ p) Oᵀ` equal to `diag(P/n, …, P/n, q)`, where `p = (π, q)` and `P = ∑ π`. -/
theorem exists_constr (π : Fin n → ℝ) (q : J → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hqπ : ∀ j a, q j ≤ π a) (hsum : ∑ a, π a + ∑ j, q j = 1) :
    ∃ O ∈ orthogonalGroup ((Fin n ⊕ J) × (Fin n ⊕ J)) ℝ,
      partialTraceB (O * diagonal (fun x => Sum.elim π q x.1 * Sum.elim π q x.2) * Oᵀ) =
        diagonal (Sum.elim (fun _ => (∑ a, π a) / n) q) ∧
      partialTraceA (O * diagonal (fun x => Sum.elim π q x.1 * Sum.elim π q x.2) * Oᵀ) =
        diagonal (Sum.elim (fun _ => (∑ a, π a) / n) q) := by
  set P := ∑ a, π a with hPdef
  set Q := ∑ j, q j with hQdef
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnq : ∀ j, (n : ℝ) * q j ≤ P := by
    intro j
    have : ∑ _a : Fin n, q j ≤ ∑ a, π a := Finset.sum_le_sum (fun a _ => hqπ j a)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => hq j)
  have hP : 0 < P := by
    by_contra h
    push Not at h
    have hq0 : ∀ j, q j = 0 := fun j =>
      le_antisymm (by nlinarith [hnq j, hq j]) (hq j)
    have : Q = 0 := Finset.sum_eq_zero (fun j _ => hq0 j)
    linarith
  obtain ⟨r, hr⟩ := exists_binPacking (n := n) q hq (fun j => by nlinarith [hnq j, hq j])
  set Wt : Fin n → ℝ := fun c => ∑ j with r j = c, q j with hWt
  set β : Fin n → ℝ := fun c => (1 / n - Wt c) / P with hβdef
  have hβ0 : ∀ c, 0 ≤ β c := fun c => div_nonneg (by linarith [hr c]) hP.le
  have hWtsum : ∑ c, Wt c = Q := Finset.sum_fiberwise Finset.univ r q
  have hβ1 : ∑ c, β c = 1 := by
    simp only [hβdef]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hWtsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, div_eq_one_iff_eq hP.ne']
    field_simp
    linarith
  have hβW : ∀ c, P * β c + Wt c = 1 / n := by
    intro c
    simp only [hβdef]
    field_simp
    ring
  have hSH : ∀ s : Fin n, ∃ G ∈ orthogonalGroup (Fin n) ℝ,
      ∀ a, (G * diagonal (lamS π s) * Gᵀ) a a = ∑ c, β c * lamS π s (a - c) :=
    fun s => schurHorn _ _ (majOn_circulant β (lamS π s) hβ0 hβ1)
  choose W hWmem hW using hSH
  refine ⟨constrMat W r, constrMat_mem hWmem r, ?_, ?_⟩
  · rw [constrMat_conj, partialTraceB_sectorState]
    congr 1
    funext u
    rcases u with a | j
    · simp only [Sum.elim_inl, hW]
      exact row_T π q r β a hβW
    · simp only [Sum.elim_inr]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, sum_sub_eq π (r j), ← hPdef, ← hQdef,
        hsum, mul_one]
  · rw [constrMat_conj, partialTraceA_sectorState]
    congr 1
    funext u
    rcases u with b | j
    · simp only [Sum.elim_inl, hW]
      exact col_T π q r β b hβW
    · simp only [Sum.elim_inr]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, sum_sub_eq π (r j), ← hPdef, ← hQdef,
        hsum, one_mul]

end Construction

/-! ## Transport to `Fin d` -/

theorem partialTraceB_submatrix_prodCongr {X Y X' Y' R : Type*} [Fintype Y] [Fintype Y']
    [AddCommMonoid R] (ρ : Matrix (X × Y) (X × Y) R) (e₁ : X' ≃ X) (e₂ : Y' ≃ Y) :
    partialTraceB (ρ.submatrix (e₁.prodCongr e₂) (e₁.prodCongr e₂)) =
      (partialTraceB ρ).submatrix e₁ e₁ := by
  ext a a'
  simp only [partialTraceB, Matrix.of_apply, Matrix.submatrix_apply, Equiv.prodCongr_apply,
    Prod.map_apply]
  exact Fintype.sum_equiv e₂ _ _ (fun b => rfl)

theorem partialTraceA_submatrix_prodCongr {X Y X' Y' R : Type*} [Fintype X] [Fintype X']
    [AddCommMonoid R] (ρ : Matrix (X × Y) (X × Y) R) (e₁ : X' ≃ X) (e₂ : Y' ≃ Y) :
    partialTraceA (ρ.submatrix (e₁.prodCongr e₂) (e₁.prodCongr e₂)) =
      (partialTraceA ρ).submatrix e₂ e₂ := by
  ext b b'
  simp only [partialTraceA, Matrix.of_apply, Matrix.submatrix_apply, Equiv.prodCongr_apply,
    Prod.map_apply]
  exact Fintype.sum_equiv e₁ _ _ (fun a => rfl)

/-- **Step 1.** For every probability vector `p` on `Fin d` sorted in decreasing order and every
`k`, there is a real orthogonal matrix `O` on `ℝ^d ⊗ ℝ^d` such that both partial traces of
`O · diag(p ⊗ p) · Oᵀ` are `diag(v_k(p))`. -/
theorem vk_reachable {d : ℕ} (p : Fin d → ℝ) (hp : Antitone p) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (k : Fin d) :
    ∃ O ∈ orthogonalGroup (Fin d × Fin d) ℝ,
      partialTraceB (O * diagonal (fun x => p x.1 * p x.2) * Oᵀ) = diagonal (vk p k) ∧
      partialTraceA (O * diagonal (fun x => p x.1 * p x.2) * Oᵀ) = diagonal (vk p k) := by
  have hkd : (k : ℕ) + 1 + (d - ((k : ℕ) + 1)) = d := by omega
  set ε : Fin ((k : ℕ) + 1) ⊕ Fin (d - ((k : ℕ) + 1)) ≃ Fin d :=
    finSumFinEquiv.trans (finCongr hkd) with hε
  have hεl : ∀ a, ((ε (Sum.inl a) : Fin d) : ℕ) = a := fun a => rfl
  have hεr : ∀ j, ((ε (Sum.inr j) : Fin d) : ℕ) = (k : ℕ) + 1 + j := fun j => rfl
  have h1 : ∀ a, ε (Sum.inl a) ≤ k := fun a => by
    rw [Fin.le_iff_val_le_val, hεl]
    omega
  have h2 : ∀ j, ¬ ε (Sum.inr j) ≤ k := fun j => by
    rw [Fin.le_iff_val_le_val, hεr]
    omega
  set π : Fin ((k : ℕ) + 1) → ℝ := fun a => p (ε (Sum.inl a)) with hπ
  set q : Fin (d - ((k : ℕ) + 1)) → ℝ := fun j => p (ε (Sum.inr j)) with hq
  have hpe : ∀ z, Sum.elim π q z = p (ε z) := by
    rintro (a | j) <;> rfl
  have hqπ : ∀ j a, q j ≤ π a := by
    intro j a
    apply hp
    rw [Fin.le_iff_val_le_val, hεl, hεr]
    omega
  have hsum : ∑ a, π a + ∑ j, q j = 1 := by
    rw [← hp1, ← Equiv.sum_comp ε p, Fintype.sum_sum_type]
  obtain ⟨O, hO, hB, hA⟩ := exists_constr π q (fun j => hp0 _) hqπ hsum
  have hstate : O.submatrix (ε.symm.prodCongr ε.symm) (ε.symm.prodCongr ε.symm) *
      diagonal (fun x : Fin d × Fin d => p x.1 * p x.2) *
      (O.submatrix (ε.symm.prodCongr ε.symm) (ε.symm.prodCongr ε.symm))ᵀ =
      (O * diagonal (fun x : _ × _ => Sum.elim π q x.1 * Sum.elim π q x.2) * Oᵀ).submatrix
        (ε.symm.prodCongr ε.symm) (ε.symm.prodCongr ε.symm) := by
    rw [← conj_submatrix, submatrix_diagonal_equiv]
    congr 3
    funext x
    simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hpe,
      Equiv.apply_symm_apply]
  have hPsum : ∑ a, π a = ∑ j with j ≤ k, p j := by
    rw [Finset.sum_filter, ← Equiv.sum_comp ε (fun j => if j ≤ k then p j else 0),
      Fintype.sum_sum_type]
    simp only [h1, h2, if_true, if_false, Finset.sum_const_zero, add_zero]
    rfl
  have hv : ∀ i, Sum.elim (fun _ => (∑ a, π a) / (((k : ℕ) + 1 : ℕ) : ℝ)) q (ε.symm i) =
      vk p k i := by
    intro i
    obtain ⟨z, rfl⟩ := ε.surjective i
    rw [Equiv.symm_apply_apply]
    rcases z with a | j
    · simp only [Sum.elim_inl, vk, if_pos (h1 a), hPsum]
      push_cast
      ring
    · simp only [Sum.elim_inr, vk, if_neg (h2 j)]
      rfl
  refine ⟨O.submatrix (ε.symm.prodCongr ε.symm) (ε.symm.prodCongr ε.symm),
    submatrix_mem_orthogonalGroup hO _, ?_, ?_⟩
  · rw [hstate, partialTraceB_submatrix_prodCongr, hB, submatrix_diagonal_equiv]
    congr 1
    funext i
    exact hv i
  · rw [hstate, partialTraceA_submatrix_prodCongr, hA, submatrix_diagonal_equiv]
    congr 1
    funext i
    exact hv i

end STUProof
