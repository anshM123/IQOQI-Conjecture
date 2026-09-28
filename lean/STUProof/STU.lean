import STUProof.Lemma5

/-!
# Symmetrically thermalizing unitaries exist in every local dimension

Conjecture of Bakhshinezhad, Clivaz, Vitagliano, Erker, Rezakhani, Huber and Friis,
*Thermodynamically optimal creation of correlations*, J. Phys. A **52**, 465303 (2019),
arXiv:1904.07942: for every Hamiltonian `H` on `ℂ^d` (the same on both sides), every `β > 0` and
every `β' ∈ [0, β]` there is a unitary `U` on `ℂ^d ⊗ ℂ^d` such that both marginals of
`U (τ_β ⊗ τ_β) U†` are equal to `τ_{β'}`, where `τ_β = e^{-βH}/Z`.

We work in the eigenbasis of `H = diag(E_0, …, E_{d-1})` with `E` sorted increasingly, so
`τ_β = gibbsState E β` is diagonal.

## Proof

1. (`vk_reachable`, `STUProof/Construction.lean`) Every `v_k(p)` is a symmetric pair of marginals
   of the orbit of `p ⊗ p`, via an explicit real orthogonal matrix (tail relabelling + real
   Schur–Horn on the cyclic diagonals of the top block).
2. (`lemma5`, `STUProof/Lemma5.lean`) `Gibbs(β')` is an explicit convex combination of the
   `v_k(Gibbs(β))`.
3. (hypothesis `KirwanSymmetricConvexity`) The set of sorted spectra `q` such that both marginals
   of some state in the unitary orbit of `diag(λ)` have spectrum `q` is convex.
4. (`partialTraceB_conj_kronecker`, `partialTraceA_conj_kronecker`) Local unitaries `V ⊗ W`
   rotate both marginals to `diag(q) = τ_{β'}`.

## Main results

* `STUProof.stu_exists`: the conjecture, assuming `KirwanSymmetricConvexity d`
  (`stu_exists_all`: for all `d` at once).
* `STUProof.stu_of_mem_symMarginalSpectra`: unconditional reduction; an STU exists as soon as
  `Gibbs(β')` is a symmetric marginal spectrum of `Gibbs(β) ⊗ Gibbs(β)`.
* `STUProof.vk_mem_symMarginalSpectra`: unconditional; every `v_k(p)` lies in the set of
  symmetric marginal spectra (with explicit orthogonal unitaries).
* `STUProof.symMarginalSpectra_eq_charpoly`, `STUProof.symMarginalSpectra_eq`: the set in the
  hypothesis described by characteristic polynomials (eigenvalue lists) and by exactly diagonal
  marginals (the "Weyl chamber" form of Kirwan's theorem).
-/

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace STUProof

/-! ## Local unitaries and partial traces (Step 4) -/

section LocalUnitaries

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem star_ite' {p : Prop} [Decidable p] (a b : ℂ) :
    star (if p then a else b) = if p then star a else star b := by
  split_ifs <;> rfl

omit [DecidableEq m] in
theorem conj_apply (A ρ : Matrix m m ℂ) (i j : m) :
    (A * ρ * star A) i j = ∑ x, ∑ y, A i x * ρ x y * star (A j y) := by
  simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sum_mul_star_eq_one {W : Matrix m m ℂ} (hW : star W * W = 1) (e e' : m) :
    ∑ b, W b e * star (W b e') = if e' = e then 1 else 0 := by
  have := congrFun (congrFun hW e') e
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

omit [DecidableEq m] in
theorem partialTraceB_conj_kronecker_one (V : Matrix m m ℂ) (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTraceB ((V ⊗ₖ (1 : Matrix n n ℂ)) * ρ * star (V ⊗ₖ (1 : Matrix n n ℂ))) =
      V * partialTraceB ρ * star V := by
  ext a a'
  rw [partialTraceB, Matrix.of_apply, conj_apply]
  simp only [conj_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, star_ite', star_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [partialTraceB, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]

theorem partialTraceB_conj_one_kronecker (W : Matrix n n ℂ) (hW : star W * W = 1)
    (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTraceB (((1 : Matrix m m ℂ) ⊗ₖ W) * ρ * star ((1 : Matrix m m ℂ) ⊗ₖ W)) =
      partialTraceB ρ := by
  ext a a'
  rw [partialTraceB, Matrix.of_apply, partialTraceB, Matrix.of_apply]
  simp only [conj_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, ite_mul, one_mul,
    zero_mul, star_ite', star_zero, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  have h : ∀ e', ∑ b, W b e * ρ (a, e) (a', e') * star (W b e') =
      ρ (a, e) (a', e') * (if e' = e then 1 else 0) := by
    intro e'
    rw [← sum_mul_star_eq_one hW e e', Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [DecidableEq n] in
theorem partialTraceA_conj_one_kronecker (W : Matrix n n ℂ) (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTraceA (((1 : Matrix m m ℂ) ⊗ₖ W) * ρ * star ((1 : Matrix m m ℂ) ⊗ₖ W)) =
      W * partialTraceA ρ * star W := by
  ext b b'
  rw [partialTraceA, Matrix.of_apply, conj_apply]
  simp only [conj_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, ite_mul, one_mul,
    zero_mul, star_ite', star_zero, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [partialTraceA, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]

theorem partialTraceA_conj_kronecker_one (V : Matrix m m ℂ) (hV : star V * V = 1)
    (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTraceA ((V ⊗ₖ (1 : Matrix n n ℂ)) * ρ * star (V ⊗ₖ (1 : Matrix n n ℂ))) =
      partialTraceA ρ := by
  ext b b'
  rw [partialTraceA, Matrix.of_apply, partialTraceA, Matrix.of_apply]
  simp only [conj_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, star_ite', star_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  have h : ∀ a', ∑ c, V c a * ρ (a, b) (a', b') * star (V c a') =
      ρ (a, b) (a', b') * (if a' = a then 1 else 0) := by
    intro a'
    rw [← sum_mul_star_eq_one hV a a', Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Step 4 (A side).** For a unitary `W`, `Tr_B((V ⊗ W) ρ (V ⊗ W)†) = V Tr_B(ρ) V†`. -/
theorem partialTraceB_conj_kronecker (V : Matrix m m ℂ) {W : Matrix n n ℂ}
    (hW : W ∈ unitaryGroup n ℂ) (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTraceB ((V ⊗ₖ W) * ρ * star (V ⊗ₖ W)) = V * partialTraceB ρ * star V := by
  set A := V ⊗ₖ (1 : Matrix n n ℂ) with hA
  set B := (1 : Matrix m m ℂ) ⊗ₖ W with hB
  have hsplit : V ⊗ₖ W = A * B := by
    rw [hA, hB, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have e : A * B * ρ * star (A * B) = A * (B * ρ * star B) * star A := by
    simp only [star_mul, Matrix.mul_assoc]
  rw [hsplit, e, hA, partialTraceB_conj_kronecker_one, hB,
    partialTraceB_conj_one_kronecker W ((mem_unitaryGroup_iff').1 hW)]

/-- **Step 4 (B side).** For a unitary `V`, `Tr_A((V ⊗ W) ρ (V ⊗ W)†) = W Tr_A(ρ) W†`. -/
theorem partialTraceA_conj_kronecker {V : Matrix m m ℂ} (hV : V ∈ unitaryGroup m ℂ)
    (W : Matrix n n ℂ) (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTraceA ((V ⊗ₖ W) * ρ * star (V ⊗ₖ W)) = W * partialTraceA ρ * star W := by
  set A := V ⊗ₖ (1 : Matrix n n ℂ) with hA
  set B := (1 : Matrix m m ℂ) ⊗ₖ W with hB
  have hsplit : V ⊗ₖ W = B * A := by
    rw [hA, hB, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have e : B * A * ρ * star (B * A) = B * (A * ρ * star A) * star B := by
    simp only [star_mul, Matrix.mul_assoc]
  rw [hsplit, e, hB, partialTraceA_conj_one_kronecker, hA,
    partialTraceA_conj_kronecker_one V ((mem_unitaryGroup_iff').1 hV)]

end LocalUnitaries

/-! ## Real orthogonal matrices as complex unitaries -/

section Complexify

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem star_map_ofReal (O : Matrix ι ι ℝ) :
    star (O.map Complex.ofRealHom) = (Oᵀ).map Complex.ofRealHom := by
  ext i j
  simp [Matrix.star_apply, Complex.conj_ofReal]

theorem map_ofReal_mem_unitaryGroup {O : Matrix ι ι ℝ} (hO : O ∈ orthogonalGroup ι ℝ) :
    O.map Complex.ofRealHom ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff, star_map_ofReal, ← Matrix.map_mul,
    (mem_orthogonalGroup_iff _ _).1 hO]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem conj_map_ofReal (O : Matrix ι ι ℝ) (w : ι → ℝ) :
    O.map Complex.ofRealHom * diagonal (fun x => (w x : ℂ)) * star (O.map Complex.ofRealHom) =
      (O * diagonal w * Oᵀ).map Complex.ofRealHom := by
  rw [star_map_ofReal, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
  rfl

theorem partialTraceB_map_ofReal {m n : Type*} [Fintype n] (M : Matrix (m × n) (m × n) ℝ) :
    partialTraceB (M.map Complex.ofRealHom) = (partialTraceB M).map Complex.ofRealHom := by
  ext a a'
  simp [partialTraceB]

theorem partialTraceA_map_ofReal {m n : Type*} [Fintype m] (M : Matrix (m × n) (m × n) ℝ) :
    partialTraceA (M.map Complex.ofRealHom) = (partialTraceA M).map Complex.ofRealHom := by
  ext b b'
  simp [partialTraceA]

end Complexify

/-! ## Gibbs states and the Kirwan hypothesis -/

/-- The Gibbs state `τ_β = e^{-βH}/Z` of `H = diag(E)`, as a complex `d × d` matrix. -/
def gibbsState {d : ℕ} (E : Fin d → ℝ) (β : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal fun i => (gibbs E β i : ℂ)

theorem gibbsState_kronecker {d : ℕ} (E : Fin d → ℝ) (β : ℝ) :
    gibbsState E β ⊗ₖ gibbsState E β =
      diagonal fun x : Fin d × Fin d => ((gibbs E β x.1 * gibbs E β x.2 : ℝ) : ℂ) := by
  rw [gibbsState, diagonal_kronecker_diagonal]
  congr 1
  funext x
  push_cast
  ring

/-- The symmetric marginal spectra of the unitary orbit of `diag(w)` on `ℂ^d ⊗ ℂ^d`: the sorted
(decreasing) vectors `q` such that for some unitary `U` both marginals of `U diag(w) U†` have
eigenvalue list `q`, i.e. are unitarily similar to `diag(q)`. -/
def symMarginalSpectra {d : ℕ} (w : Fin d × Fin d → ℝ) : Set (Fin d → ℝ) :=
  {q : Fin d → ℝ | Antitone q ∧ ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ, ∃ V ∈ unitaryGroup (Fin d) ℂ,
      ∃ W ∈ unitaryGroup (Fin d) ℂ,
        V * partialTraceB (U * diagonal (fun x => (w x : ℂ)) * star U) * star V =
          diagonal (fun i => (q i : ℂ)) ∧
        W * partialTraceA (U * diagonal (fun x => (w x : ℂ)) * star U) * star W =
          diagonal (fun i => (q i : ℂ))}

/-- **Hypothesis: Kirwan's convexity theorem, symmetric slice.**

F. C. Kirwan, *Convexity properties of the moment mapping, III*, Invent. Math. **77**, 547–552
(1984): for a compact connected Lie group `K` acting on a compact connected symplectic manifold
`M` with moment map `μ`, the set `μ(M) ∩ t*_+` is a convex polytope. Apply it to `K = U(d) × U(d)`
acting by `ρ ↦ (V ⊗ W) ρ (V ⊗ W)†` on the unitary orbit `M` of `diag(w)` (a coadjoint orbit of
`U(d²)`), with moment map `ρ ↦ (Tr_B ρ, Tr_A ρ)`. Then the set of pairs of sorted marginal
spectra is convex (A. Klyachko, *Quantum marginal problem and representations of the symmetric
group*, arXiv:quant-ph/0409113), and so is its intersection with the diagonal `{(q, q)}`, which
is `symMarginalSpectra w`.

`symMarginalSpectra_eq_charpoly` restates the set with characteristic polynomials (eigenvalue
lists), and `symMarginalSpectra_eq` with exactly diagonal marginals (the Weyl-chamber form).
Only `w = p ⊗ p` with `p` a Gibbs vector is used.

This is not proved here; it is an explicit hypothesis of `stu_exists`. -/
def KirwanSymmetricConvexity (d : ℕ) : Prop :=
  ∀ w : Fin d × Fin d → ℝ, Convex ℝ (symMarginalSpectra w)

/-- The hypothesis is the "Weyl chamber" form of Kirwan's theorem: `q ∈ symMarginalSpectra w`
iff `q` is sorted and some state in the orbit has both marginals exactly `diag(q)`. -/
theorem symMarginalSpectra_eq {d : ℕ} (w : Fin d × Fin d → ℝ) :
    symMarginalSpectra w = {q : Fin d → ℝ | Antitone q ∧ ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * diagonal (fun x => (w x : ℂ)) * star U) =
        diagonal (fun i => (q i : ℂ)) ∧
      partialTraceA (U * diagonal (fun x => (w x : ℂ)) * star U) =
        diagonal (fun i => (q i : ℂ))} := by
  ext q
  constructor
  · rintro ⟨hq, U, hU, V, hV, W, hW, hB, hA⟩
    refine ⟨hq, (V ⊗ₖ W) * U, mul_mem (kronecker_mem_unitary hV hW) hU, ?_, ?_⟩
    · have e : (V ⊗ₖ W) * U * diagonal (fun x => (w x : ℂ)) * star ((V ⊗ₖ W) * U) =
          (V ⊗ₖ W) * (U * diagonal (fun x => (w x : ℂ)) * star U) * star (V ⊗ₖ W) := by
        simp only [star_mul, Matrix.mul_assoc]
      rw [e, partialTraceB_conj_kronecker V hW, hB]
    · have e : (V ⊗ₖ W) * U * diagonal (fun x => (w x : ℂ)) * star ((V ⊗ₖ W) * U) =
          (V ⊗ₖ W) * (U * diagonal (fun x => (w x : ℂ)) * star U) * star (V ⊗ₖ W) := by
        simp only [star_mul, Matrix.mul_assoc]
      rw [e, partialTraceA_conj_kronecker hV W, hA]
  · rintro ⟨hq, U, hU, hB, hA⟩
    refine ⟨hq, U, hU, 1, one_mem _, 1, one_mem _, ?_, ?_⟩
    · rw [hB, Matrix.one_mul, star_one, Matrix.mul_one]
    · rw [hA, Matrix.one_mul, star_one, Matrix.mul_one]

/-! ## The hypothesis in terms of characteristic polynomials -/

/-- Two Hermitian matrices are unitarily similar iff they have the same characteristic
polynomial (spectral theorem). -/
theorem exists_unitary_conj_iff_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∃ V ∈ unitaryGroup n ℂ, V * A * star V = B) ↔ A.charpoly = B.charpoly := by
  constructor
  · rintro ⟨V, hV, rfl⟩
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, (mem_unitaryGroup_iff').1 hV,
      Matrix.one_mul]
  · intro h
    have heig := (hA.eigenvalues_eq_eigenvalues_iff hB).2 h
    have sA := hA.spectral_theorem
    have sB := hB.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at sA sB
    rw [heig] at sA
    set UA := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUAdef
    set UB := (hB.eigenvectorUnitary : Matrix n n ℂ) with hUBdef
    have hUA : star UA * UA = 1 := Unitary.coe_star_mul_self _
    have key : ∀ X : Matrix n n ℂ, star UA * (UA * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hUA, Matrix.one_mul]
    refine ⟨UB * star UA, mul_mem hB.eigenvectorUnitary.2 (Unitary.star_mem hA.eigenvectorUnitary.2), ?_⟩
    rw [sA]
    conv_rhs => rw [sB]
    rw [star_mul, star_star]
    simp only [Matrix.mul_assoc, key]

theorem partialTraceB_isHermitian {m n : Type*} [Fintype n] {ρ : Matrix (m × n) (m × n) ℂ}
    (h : ρ.IsHermitian) : (partialTraceB ρ).IsHermitian := by
  ext a a'
  simp only [conjTranspose_apply, partialTraceB, of_apply, star_sum]
  exact Finset.sum_congr rfl (fun b _ => by rw [← conjTranspose_apply, h])

theorem partialTraceA_isHermitian {m n : Type*} [Fintype m] {ρ : Matrix (m × n) (m × n) ℂ}
    (h : ρ.IsHermitian) : (partialTraceA ρ).IsHermitian := by
  ext b b'
  simp only [conjTranspose_apply, partialTraceA, of_apply, star_sum]
  exact Finset.sum_congr rfl (fun a _ => by rw [← conjTranspose_apply, h])

theorem isHermitian_diagonal_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) :
    (diagonal (fun i => (q i : ℂ))).IsHermitian := by
  rw [IsHermitian, diagonal_conjTranspose]
  congr 1
  funext i
  simp

theorem conj_diagonal_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (w : ι → ℝ) : (U * diagonal (fun x => (w x : ℂ)) * star U).IsHermitian := by
  rw [star_eq_conjTranspose]
  exact isHermitian_mul_mul_conjTranspose U (isHermitian_diagonal_ofReal w)

open Polynomial in
theorem charpoly_diagonal_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) :
    (diagonal (fun i => (q i : ℂ))).charpoly = ∏ i, (X - C (q i : ℂ)) :=
  charpoly_diagonal _

open Polynomial in
/-- The set `symMarginalSpectra w` in the language of characteristic polynomials: `q` is sorted
and, for some unitary `U`, both marginals of `U diag(w) U†` have characteristic polynomial
`∏ᵢ (X - qᵢ)`, i.e. eigenvalue list `q`. -/
theorem symMarginalSpectra_eq_charpoly {d : ℕ} (w : Fin d × Fin d → ℝ) :
    symMarginalSpectra w = {q : Fin d → ℝ | Antitone q ∧ ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      (partialTraceB (U * diagonal (fun x => (w x : ℂ)) * star U)).charpoly =
        ∏ i, (X - C (q i : ℂ)) ∧
      (partialTraceA (U * diagonal (fun x => (w x : ℂ)) * star U)).charpoly =
        ∏ i, (X - C (q i : ℂ))} := by
  ext q
  constructor
  · rintro ⟨hq, U, hU, V, hV, W, hW, hB, hA⟩
    refine ⟨hq, U, hU, ?_, ?_⟩
    · rw [← charpoly_diagonal_ofReal,
        ← (exists_unitary_conj_iff_charpoly
          (partialTraceB_isHermitian (conj_diagonal_isHermitian U w))
          (isHermitian_diagonal_ofReal q))]
      exact ⟨V, hV, hB⟩
    · rw [← charpoly_diagonal_ofReal,
        ← (exists_unitary_conj_iff_charpoly
          (partialTraceA_isHermitian (conj_diagonal_isHermitian U w))
          (isHermitian_diagonal_ofReal q))]
      exact ⟨W, hW, hA⟩
  · rintro ⟨hq, U, hU, hB, hA⟩
    rw [← charpoly_diagonal_ofReal] at hB hA
    obtain ⟨V, hV, hV'⟩ := (exists_unitary_conj_iff_charpoly
      (partialTraceB_isHermitian (conj_diagonal_isHermitian U w))
      (isHermitian_diagonal_ofReal q)).2 hB
    obtain ⟨W, hW, hW'⟩ := (exists_unitary_conj_iff_charpoly
      (partialTraceA_isHermitian (conj_diagonal_isHermitian U w))
      (isHermitian_diagonal_ofReal q)).2 hA
    exact ⟨hq, U, hU, V, hV, W, hW, hV', hW'⟩

/-! ## Step 1 in the language of the hypothesis -/

theorem vk_antitone {d : ℕ} (p : Fin d → ℝ) (hp : Antitone p) (k : Fin d) :
    Antitone (vk p k) := by
  have havg : ∀ j, k < j → p j ≤ (∑ l with l ≤ k, p l) / ((k : ℕ) + 1 : ℝ) := by
    intro j hkj
    rw [← psum_extN, le_div_iff₀ (by positivity), psum]
    have h : ∑ i ∈ range ((k : ℕ) + 1), p j ≤ ∑ i ∈ range ((k : ℕ) + 1), extN p i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < d := by rw [Finset.mem_range] at hi; omega
      rw [extN_lt p hi']
      apply hp
      rw [Fin.le_iff_val_le_val]
      rw [Fin.lt_def] at hkj
      simp only
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    push_cast at h
    linarith
  intro i j hij
  unfold vk
  by_cases hj : j ≤ k
  · rw [if_pos hj, if_pos (hij.trans hj)]
  · rw [if_neg hj]
    by_cases hi : i ≤ k
    · rw [if_pos hi]
      exact havg j (lt_of_not_ge hj)
    · rw [if_neg hi]
      exact hp hij

/-- **Step 1, unconditional.** For every sorted probability vector `p` and every `k`, `v_k(p)`
is a symmetric marginal spectrum of the orbit of `p ⊗ p` (realized by a real orthogonal `U`). -/
theorem vk_mem_symMarginalSpectra {d : ℕ} (p : Fin d → ℝ) (hp : Antitone p)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (k : Fin d) :
    vk p k ∈ symMarginalSpectra (fun x => p x.1 * p x.2) := by
  obtain ⟨O, hO, hB, hA⟩ := vk_reachable p hp hp0 hp1 k
  refine ⟨vk_antitone p hp k, O.map Complex.ofRealHom, map_ofReal_mem_unitaryGroup hO,
    1, one_mem _, 1, one_mem _, ?_, ?_⟩
  · rw [conj_map_ofReal, partialTraceB_map_ofReal, hB, Matrix.one_mul, star_one, Matrix.mul_one,
      Matrix.diagonal_map (map_zero _)]
    rfl
  · rw [conj_map_ofReal, partialTraceA_map_ofReal, hA, Matrix.one_mul, star_one, Matrix.mul_one,
      Matrix.diagonal_map (map_zero _)]
    rfl

/-! ## The main theorem -/

/-- **Reduction.** If `Gibbs(β')` is a symmetric marginal spectrum of `Gibbs(β) ⊗ Gibbs(β)`, then
a symmetrically thermalizing unitary exists. (`stu_exists` uses the Kirwan hypothesis only to
prove this membership.) -/
theorem stu_of_mem_symMarginalSpectra {d : ℕ} (E : Fin d → ℝ) (β β' : ℝ)
    (hq : gibbs E β' ∈ symMarginalSpectra (fun x => gibbs E β x.1 * gibbs E β x.2)) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' := by
  rw [symMarginalSpectra_eq] at hq
  obtain ⟨-, U, hU, hB, hA⟩ := hq
  refine ⟨U, hU, ?_, ?_⟩
  · rw [gibbsState_kronecker, hB]
    rfl
  · rw [gibbsState_kronecker, hA]
    rfl

/-- Steps 1–3: under the Kirwan hypothesis, `Gibbs(β')` is a symmetric marginal spectrum of
`Gibbs(β) ⊗ Gibbs(β)`. -/
theorem gibbs_mem_symMarginalSpectra {d : ℕ} (hK : KirwanSymmetricConvexity d) (hd : 0 < d)
    (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ} (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    gibbs E β' ∈ symMarginalSpectra (fun x => gibbs E β x.1 * gibbs E β x.2) := by
  obtain ⟨c, hc0, hc1, hcv⟩ := lemma5 hd E hE hβ hβ'0 hβ'β
  rw [← hcv]
  exact (hK _).sum_mem (fun k _ => hc0 k) hc1 (fun k _ => vk_mem_symMarginalSpectra _
    (gibbs_antitone E hE hβ.le) (gibbs_nonneg E β) (gibbs_sum hd E β) k)

/-- **Symmetrically thermalizing unitaries exist in every local dimension** (conjecture of
arXiv:1904.07942), assuming Kirwan's convexity theorem in the form `KirwanSymmetricConvexity d`.

For energies `E_0 ≤ … ≤ E_{d-1}`, `β > 0` and `0 ≤ β' ≤ β` there is a unitary `U` on
`ℂ^d ⊗ ℂ^d` such that both marginals of `U (τ_β ⊗ τ_β) U†` equal `τ_{β'}`. -/
theorem stu_exists {d : ℕ} (hK : KirwanSymmetricConvexity d) (E : Fin d → ℝ) (hE : Monotone E)
    (β β' : ℝ) (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, one_mem _, ?_, ?_⟩ <;> ext i <;> exact i.elim0
  exact stu_of_mem_symMarginalSpectra E β β'
    (gibbs_mem_symMarginalSpectra hK hd E hE hβ hβ'0 hβ'β)

/-- `stu_exists` for all local dimensions at once. -/
theorem stu_exists_all (hK : ∀ d, KirwanSymmetricConvexity d) :
    ∀ (d : ℕ) (E : Fin d → ℝ), Monotone E → ∀ β β' : ℝ, 0 < β → 0 ≤ β' → β' ≤ β →
      ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
        partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
        partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  fun d E hE β β' hβ hβ'0 hβ'β => stu_exists (hK d) E hE β β' hβ hβ'0 hβ'β

end STUProof
