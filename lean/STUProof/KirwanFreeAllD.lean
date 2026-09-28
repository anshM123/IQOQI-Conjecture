import STUProof.KirwanFreeU
import STUProof.CrossUnif

/-!
# The STU conjecture in all dimensions from one explicit inequality

Interval uniformisations of all intervals `[lo, hi]` of the `n`-box (`IntervalUnifAll n`) come from
explicit constructions (P-UNIF):
* `[0, n-1]`: the all-ones square `J` (`isIntervalUnif_boxJ`);
* `[0, hi]`, `hi ≤ n-2`: the renewal square `U^hi_n` (`isIntervalUnif_renU`);
* `[lo, n-1]`, `lo ≥ 1`: the complement `J - U^{lo-1}_n` (`IsIntervalUnif.compl`);
* `[lo, hi]`, `1 ≤ lo ≤ hi ≤ n-2`: the cross construction `X(n, lo, hi)` (`isIntervalUnif_crossX`),
  which needs the short-run inequality `XShortNonneg n lo hi`.

With `stu_exists_of_intervalUnif` this reduces the STU conjecture in dimension `d` to
`XShortNonneg n lo hi` for all `n ≤ d` and `1 ≤ lo ≤ hi ≤ n-2` (`stu_exists_of_shortNonneg`), and in
all dimensions to `XShortNonneg` for all `n` (`stu_exists_all_of_shortNonneg`).
-/

open Matrix Finset
open scoped Kronecker

namespace STUProof

/-- Interval uniformisations of all intervals of the `n`-box, given the short-run inequality for
the cross construction. -/
theorem intervalUnifAll_of_shortNonneg {n : ℕ}
    (h : ∀ lo hi, 1 ≤ lo → lo ≤ hi → hi + 2 ≤ n → XShortNonneg n lo hi) : IntervalUnifAll n := by
  intro lo hi hlohi hhi
  by_cases hlo : lo = 0
  · subst hlo
    by_cases hh : hi + 1 = n
    · obtain rfl : hi = n - 1 := by omega
      exact ⟨boxJ n, isIntervalUnif_boxJ (by omega)⟩
    · exact ⟨renU n hi, isIntervalUnif_renU (by omega)⟩
  · obtain ⟨m, rfl⟩ : ∃ m, lo = m + 1 := ⟨lo - 1, by omega⟩
    by_cases hh : hi + 1 = n
    · obtain rfl : hi = n - 1 := by omega
      exact ⟨_, (isIntervalUnif_renU (show m + 2 ≤ n by omega)).compl (by omega)⟩
    · exact ⟨crossX n (m + 1) hi,
        isIntervalUnif_crossX (by omega) hlohi (by omega) (h (m + 1) hi (by omega) hlohi (by omega))⟩

/-- **The STU conjecture in dimension `d` from the short-run inequality** `XShortNonneg n lo hi`
(for all `n ≤ d`, `1 ≤ lo ≤ hi ≤ n-2`): no Kirwan convexity and no hook decompositions. -/
theorem stu_exists_of_shortNonneg {d : ℕ}
    (h : ∀ n ≤ d, ∀ lo hi, 1 ≤ lo → lo ≤ hi → hi + 2 ≤ n → XShortNonneg n lo hi)
    (E : Fin d → ℝ) (hE : Monotone E) (β β' : ℝ) (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  stu_exists_of_intervalUnif (fun n hn => intervalUnifAll_of_shortNonneg (h n hn)) E hE β β' hβ
    hβ'0 hβ'β

/-- **The STU conjecture in all dimensions from the short-run inequality** for all `n`. -/
theorem stu_exists_all_of_shortNonneg
    (h : ∀ n lo hi, 1 ≤ lo → lo ≤ hi → hi + 2 ≤ n → XShortNonneg n lo hi) :
    ∀ (d : ℕ) (E : Fin d → ℝ), Monotone E → ∀ β β' : ℝ, 0 < β → 0 ≤ β' → β' ≤ β →
      ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
        partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
        partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  fun _ E hE β β' hβ h0 h1 =>
    stu_exists_of_shortNonneg (fun n _ lo hi => h n lo hi) E hE β β' hβ h0 h1

end STUProof
