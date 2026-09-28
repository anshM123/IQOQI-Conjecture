import STUProof.HookCertificates

/-!
# Split kernel checks of integer hook decompositions

For the larger certificates (`STUProof/HookCert{n}.lean`, `n = 21, 23, …, 39`) a single
`decide +kernel` over all constraints of `IsHookDecompositionNat` needs too much memory. The
constraints are therefore checked in small pieces: the runs and the rows of each hook `a`, and the
cells of each run `s`, each piece by its own `decide +kernel`. This file contains the pieces and
the lemmas that assemble them.
-/

open Finset

namespace STUProof

/-- The run constraints of hook `a` of an integer-scaled hook decomposition. -/
def HookRunNat (n D : ℕ) (y : ℕ → ℕ → ℕ → ℕ) (a : ℕ) : Prop :=
  ∀ s ≤ a, ∑ i ∈ range (n - s), y a s i = D

/-- The row constraints of hook `a` of an integer-scaled hook decomposition. -/
def HookRowNat (n D : ℕ) (y : ℕ → ℕ → ℕ → ℕ) (a : ℕ) : Prop :=
  ∀ r < n, n * (y a 0 r + ∑ s ∈ Icc 1 a,
    ((if r + s ≤ n - 1 then y a s r else 0) + (if s ≤ r then y a s (r - s) else 0))) =
      (2 * a + 1) * D

/-- The cell constraints of the run `s` of an integer-scaled hook decomposition. -/
def HookCellNat (n D : ℕ) (y : ℕ → ℕ → ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ i < n - s, ∑ a ∈ Ico s n, y a s i = D

theorem isHookDecompositionNat_of_split {n D : ℕ} {y : ℕ → ℕ → ℕ → ℕ}
    (h1 : ∀ a < n, HookRunNat n D y a) (h2 : ∀ a < n, HookRowNat n D y a)
    (h3 : ∀ s < n, HookCellNat n D y s) : IsHookDecompositionNat n D y :=
  ⟨h1, h2, h3⟩

theorem forall_lt_zero (P : ℕ → Prop) : ∀ a < 0, P a :=
  fun a ha => absurd ha (Nat.not_lt_zero a)

/-- `∀ a < n + 1, P a` from `∀ a < n, P a` and `P n`. -/
theorem forall_lt_succ_of {P : ℕ → Prop} {n : ℕ} (h : ∀ a < n, P a) (hn : P n) :
    ∀ a < n + 1, P a := by
  intro a ha
  by_cases h' : a < n
  · exact h a h'
  · obtain rfl : a = n := by omega
    exact hn

end STUProof
