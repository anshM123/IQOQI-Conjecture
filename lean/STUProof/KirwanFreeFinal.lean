import STUProof.KirwanFreeU
import STUProof.UnifAllN

/-!
# The STU conjecture in every dimension, unconditionally

Conjecture of Bakhshinezhad, Clivaz, Vitagliano, Erker, Rezakhani, Huber, Friis,
J. Phys. A 52, 465303 (2019), arXiv:1904.07942: for every local dimension `d`, energies
`E_0 ≤ … ≤ E_{d-1}` and inverse temperatures `0 ≤ β' ≤ β`, `β > 0`, there is a (symmetrically
thermalizing) unitary `U` on `ℂ^d ⊗ ℂ^d` such that both marginals of `U (τ_β ⊗ τ_β) U†` equal
`τ_{β'}`.

Proof: `stu_exists_of_intervalUnif` (the Kirwan-free construction, `STUProof/KirwanFreeU.lean`)
needs interval uniformisations of all intervals of all boxes (`IntervalUnifAll n`), and
`intervalUnifAll_all` (`STUProof/UnifAllN.lean`) provides them for every `n`: renewal squares,
their complements, and the one-dipole T/H/G construction of P-PROOF. No hypothesis remains.
-/

open Matrix
open scoped Kronecker

namespace STUProof

/-- **Symmetrically thermalizing unitaries exist in every local dimension** (the conjecture of
arXiv:1904.07942), with no hypotheses: no Kirwan convexity, no hook decompositions and no open
inequality (the analytic facts F1-F6 are proved for all `K` in `STUProof/UnifFacts.lean`). -/
theorem stu_exists_unconditional :
    ∀ (d : ℕ) (E : Fin d → ℝ), Monotone E → ∀ β β' : ℝ, 0 < β → 0 ≤ β' → β' ≤ β →
      ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
        partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
        partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  fun _ E hE β β' hβ h0 h1 =>
    stu_exists_of_intervalUnif (fun n _ => intervalUnifAll_all n) E hE β β' hβ h0 h1

end STUProof
