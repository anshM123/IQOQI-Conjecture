import STUProof.KirwanFreeFinal

/-!
# The STU conjecture for an arbitrary Hermitian Hamiltonian

`stu_exists_unconditional` (`STUProof/KirwanFreeFinal.lean`) is stated in the eigenbasis of the
Hamiltonian: `H = diag(E)` with `E` sorted increasingly, and the thermal state is the diagonal
matrix `gibbsState E β`. This file removes that normalisation.

* `thermalState H β = e^{-βH} / Tr e^{-βH}` for a complex square matrix `H`, where `e^{-βH}` is
  Mathlib's matrix exponential `NormedSpace.exp` (the exponential series).
* `thermalState_diag`: for `H = diag(E)` with `E` real, `thermalState H β = gibbsState E β`.
* `thermalState_conj`: `thermalState (V H V†) β = V (thermalState H β) V†` for unitary `V`.
* `exists_sorted_diagonalization`: a Hermitian `H` equals `V diag(E) V†` with `V` unitary and `E`
  sorted increasingly (Mathlib's spectral theorem, then `Tuple.sort` on the eigenvalues).
* `stu_exists_hermitian`: the conjecture of arXiv:1904.07942 for every Hermitian `H` on `ℂ^d`.

## Proof of `stu_exists_hermitian`

Write `H = V diag(E) V†` with `E` monotone. Then `τ_γ(H) = V τ_γ(E) V†` for every `γ`
(`exists_thermalState_eq_conj`). `stu_exists_unconditional` gives a unitary `U₀` such that both
marginals of `U₀ (τ_β(E) ⊗ τ_β(E)) U₀†` are `τ_{β'}(E)`. Put `W = V ⊗ V` and `U = W U₀ W†`. Then
`τ_β(H) ⊗ τ_β(H) = W (τ_β(E) ⊗ τ_β(E)) W†`, so `U (τ_β(H) ⊗ τ_β(H)) U† = W (U₀ (…) U₀†) W†`.
Local unitaries rotate the marginals, `Tr_B (W ρ W†) = V (Tr_B ρ) V†` and
`Tr_A (W ρ W†) = V (Tr_A ρ) V†` (`partialTraceB_conj_kronecker`, `partialTraceA_conj_kronecker`,
`STUProof/STU.lean`). Both marginals are therefore `V τ_{β'}(E) V† = τ_{β'}(H)`.

The dimension `d` is arbitrary; `d = 0` needs no separate case.
-/

open Matrix
open scoped Kronecker

noncomputable section

namespace STUProof

/-! ## The thermal state of a Hamiltonian -/

/-- The thermal (Gibbs) state `τ_β(H) = e^{-βH} / Tr e^{-βH}` of a Hamiltonian `H` at inverse
temperature `β`. Here `NormedSpace.exp` is Mathlib's matrix exponential. -/
def thermalState {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (β : ℝ) :
    Matrix n n ℂ :=
  (1 / (NormedSpace.exp ((-β) • H)).trace) • NormedSpace.exp ((-β) • H)

theorem smul_diagonal_ofReal {n : Type*} [DecidableEq n] (c : ℝ) (e : n → ℝ) :
    c • diagonal (fun i => (e i : ℂ)) = diagonal (fun i => ((c * e i : ℝ) : ℂ)) := by
  rw [← diagonal_smul]
  congr 1
  funext i
  simp [Complex.real_smul]

/-- The matrix exponential of a real diagonal matrix. -/
theorem exp_diagonal_ofReal {n : Type*} [Fintype n] [DecidableEq n] (e : n → ℝ) :
    NormedSpace.exp (diagonal (fun i => (e i : ℂ))) =
      diagonal (fun i => (Real.exp (e i) : ℂ)) := by
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  simp only [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

/-- **The definitions agree.** For `H = diag(E)` with `E` real, `e^{-βH} / Tr e^{-βH}` is the
diagonal Gibbs state `gibbsState E β` used in `stu_exists_unconditional`. -/
theorem thermalState_diag {d : ℕ} (E : Fin d → ℝ) (β : ℝ) :
    thermalState (diagonal fun i => (E i : ℂ)) β = gibbsState E β := by
  rw [thermalState, smul_diagonal_ofReal, exp_diagonal_ofReal, trace_diagonal, gibbsState,
    ← diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, gibbs]
  push_cast
  ring

/-- The thermal state is covariant under unitary conjugation of the Hamiltonian. -/
theorem thermalState_conj {n : Type*} [Fintype n] [DecidableEq n] {V : Matrix n n ℂ}
    (hV : V ∈ unitaryGroup n ℂ) (H : Matrix n n ℂ) (β : ℝ) :
    thermalState (V * H * star V) β = V * thermalState H β * star V := by
  have hVV : star V * V = 1 := (mem_unitaryGroup_iff').1 hV
  have hinv : V⁻¹ = star V := Matrix.inv_eq_left_inv hVV
  have hunit : IsUnit V := Unitary.isUnit_coe (U := ⟨V, hV⟩)
  have hexp : NormedSpace.exp ((-β) • (V * H * star V)) =
      V * NormedSpace.exp ((-β) • H) * star V := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hinv]
    exact Matrix.exp_conj V _ hunit
  have htr : (NormedSpace.exp ((-β) • (V * H * star V))).trace =
      (NormedSpace.exp ((-β) • H)).trace := by
    rw [hexp, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]
  rw [thermalState, thermalState, htr, hexp, Matrix.mul_smul, Matrix.smul_mul]

/-! ## Diagonalisation with sorted eigenvalues -/

/-- Permuting the columns of a unitary matrix gives a unitary matrix. -/
theorem submatrix_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (σ : Equiv.Perm n) : U.submatrix id σ ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff'] at hU ⊢
  rw [star_eq_conjTranspose, conjTranspose_submatrix, ← star_eq_conjTranspose]
  have h := submatrix_mul_equiv (star U) U σ (Equiv.refl n) σ
  rw [Equiv.coe_refl] at h
  rw [h, hU, submatrix_one_equiv]

theorem conj_submatrix_diagonal {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (σ : Equiv.Perm n) (e : n → ℝ) :
    U.submatrix id σ * diagonal (fun i => (e (σ i) : ℂ)) * star (U.submatrix id σ) =
      U * diagonal (fun i => (e i : ℂ)) * star U := by
  have h1 : diagonal (fun i => (e (σ i) : ℂ)) =
      (diagonal (fun i => (e i : ℂ))).submatrix σ σ :=
    (submatrix_diagonal_equiv (fun i => (e i : ℂ)) σ).symm
  rw [h1, star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

/-- **Spectral theorem with sorted eigenvalues.** A Hermitian `H` is `V diag(E) V†` with `V`
unitary and `E` sorted increasingly. -/
theorem exists_sorted_diagonalization {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) :
    ∃ V ∈ unitaryGroup (Fin d) ℂ, ∃ E : Fin d → ℝ, Monotone E ∧
      H = V * diagonal (fun i => (E i : ℂ)) * star V := by
  have hspec : H = (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      diagonal (fun i => (hH.eigenvalues i : ℂ)) *
        star (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ).submatrix id
      (Tuple.sort hH.eigenvalues),
    submatrix_mem_unitaryGroup hH.eigenvectorUnitary.2 _,
    fun i => hH.eigenvalues (Tuple.sort hH.eigenvalues i),
    Tuple.monotone_sort hH.eigenvalues, ?_⟩
  exact hspec.trans (conj_submatrix_diagonal (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    (Tuple.sort hH.eigenvalues) hH.eigenvalues).symm

/-- The thermal states of a Hermitian `H` at all temperatures are, in one sorted eigenbasis
`V`, the diagonal Gibbs states: `τ_β(H) = V τ_β(E) V†` for every `β`. -/
theorem exists_thermalState_eq_conj {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) :
    ∃ V ∈ unitaryGroup (Fin d) ℂ, ∃ E : Fin d → ℝ, Monotone E ∧
      ∀ β : ℝ, thermalState H β = V * gibbsState E β * star V := by
  obtain ⟨V, hV, E, hE, hHV⟩ := exists_sorted_diagonalization hH
  exact ⟨V, hV, E, hE, fun β => by rw [hHV, thermalState_conj hV, thermalState_diag]⟩

/-! ## Local unitaries on `ℂ^d ⊗ ℂ^d` -/

theorem star_kronecker {m n : Type*} (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    star (A ⊗ₖ B) = star A ⊗ₖ star B := by
  simp only [star_eq_conjTranspose]
  exact conjTranspose_kronecker A B

theorem conj_kronecker_conj {n : Type*} [Fintype n] (V A B : Matrix n n ℂ) :
    (V * A * star V) ⊗ₖ (V * B * star V) = (V ⊗ₖ V) * (A ⊗ₖ B) * star (V ⊗ₖ V) := by
  rw [star_kronecker, mul_kronecker_mul, mul_kronecker_mul]

/-! ## The main theorem -/

/-- **Symmetrically thermalizing unitaries exist for every Hermitian Hamiltonian** (the conjecture
of arXiv:1904.07942 in its basis-free form): for every Hermitian `H` on `ℂ^d`, `β > 0` and
`0 ≤ β' ≤ β`, some unitary `U` on `ℂ^d ⊗ ℂ^d` maps `τ_β(H) ⊗ τ_β(H)` to a state whose two
marginals are both `τ_{β'}(H)`, where `τ_β(H) = e^{-βH} / Tr e^{-βH}`. -/
theorem stu_exists_hermitian {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (β β' : ℝ) (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (thermalState H β ⊗ₖ thermalState H β) * star U) = thermalState H β' ∧
      partialTraceA (U * (thermalState H β ⊗ₖ thermalState H β) * star U) = thermalState H β' := by
  obtain ⟨V, hV, E, hE, hth⟩ := exists_thermalState_eq_conj hH
  obtain ⟨U₀, hU₀, hB, hA⟩ := stu_exists_unconditional d E hE β β' hβ h0 h1
  have hW : V ⊗ₖ V ∈ unitaryGroup (Fin d × Fin d) ℂ := kronecker_mem_unitary hV hV
  have hWW : star (V ⊗ₖ V) * (V ⊗ₖ V) = 1 := (mem_unitaryGroup_iff').1 hW
  have key : ∀ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      star (V ⊗ₖ V) * ((V ⊗ₖ V) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have hρ : (V ⊗ₖ V) * U₀ * star (V ⊗ₖ V) * (thermalState H β ⊗ₖ thermalState H β) *
      star ((V ⊗ₖ V) * U₀ * star (V ⊗ₖ V)) =
      (V ⊗ₖ V) * (U₀ * (gibbsState E β ⊗ₖ gibbsState E β) * star U₀) * star (V ⊗ₖ V) := by
    rw [hth, conj_kronecker_conj]
    simp only [star_mul, star_star, Matrix.mul_assoc, key]
  refine ⟨(V ⊗ₖ V) * U₀ * star (V ⊗ₖ V), mul_mem (mul_mem hW hU₀) (Unitary.star_mem hW), ?_, ?_⟩
  · rw [hρ, partialTraceB_conj_kronecker V hV, hB, hth]
  · rw [hρ, partialTraceA_conj_kronecker hV V, hA, hth]

end STUProof
