import STUProof.KirwanFreeAllD

/-!
# The short-run inequality for small boxes (kernel computation)

The cross construction `crossX` is real-valued. Its definition only uses rational operations, so we
mirror it over `ℚ` (`crossXQ`, with the same formulas), prove `(crossXQ n lo hi i j : ℝ) =
crossX n lo hi i j` (`crossXQ_cast`), and check `0 ≤ crossXQ n lo hi i j` on all short runs of all
boxes `n ≤ 8` with the Lean kernel (`decide +kernel`, exact rational arithmetic). This proves
`XShortNonneg n lo hi` for `n ≤ 8` (`xShortNonneg_le_8`), and hence, independently of the hook
certificates, the STU conjecture for `d ≤ 8` along the interval-uniformisation route
(`stu_exists_le_8_of_unif`).
-/

open Matrix Finset
open scoped Kronecker

namespace STUProof

/-! ## Rational mirror of the construction -/

/-- `renK` over `ℚ`. -/
def renKQ (n m : ℕ) : ℚ := (n : ℚ) - m - 1

/-- `renH` over `ℚ`. -/
def renHQ (n m ℓ : ℕ) : ℚ :=
  if 1 ≤ ℓ ∧ ℓ ≤ m + 1 then 1 - renKQ n m ^ 2 / (((n : ℚ) - ℓ) * ((n : ℚ) - ℓ + 1)) else 0

/-- `renA` over `ℚ`. -/
def renAQ (n m p : ℕ) : ℚ := ∑ t ∈ range (m + 2), (-1 : ℚ) ^ t * renHQ n m (p + t)

/-- `renU` over `ℚ`. -/
def renUQ (n m i j : ℕ) : ℚ :=
  if i < n ∧ j < n then
    renAQ n m (i - j + (j - i) + 1) + renAQ n m (min (i + j + 2) (2 * n - (i + j)))
  else 0

/-- `boxJ` over `ℚ`. -/
def boxJQ (n i j : ℕ) : ℚ := if i < n ∧ j < n then 1 else 0

/-- `place` over `ℚ`. -/
def placeQ (t : ℕ) (V : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ :=
  if t ≤ i ∧ t ≤ j then V (i - t) (j - t) else 0

/-- `avgPlace` over `ℚ`. -/
def avgPlaceQ (T : ℕ) (V : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ := (∑ t ∈ range T, placeQ t V i j) / T

/-- `crossTheta` over `ℚ`. -/
def crossThetaQ (lo hi : ℕ) : ℚ := 1 - (lo : ℚ) ^ 2 / (2 * ((hi : ℚ) + 1) ^ 2)

/-- `crossX` over `ℚ`. -/
def crossXQ (n lo hi i j : ℕ) : ℚ :=
  crossThetaQ lo hi * renUQ n hi i j +
    (1 - crossThetaQ lo hi) * avgPlaceQ (n + 1 - (hi + 1)) (boxJQ (hi + 1)) i j -
    1 / 2 * renUQ n (lo - 1) i j -
    1 / 2 * avgPlaceQ (n + 1 - (hi + 1)) (renUQ (hi + 1) (lo - 1)) i j

/-! ## Casts -/

theorem renHQ_cast (n m ℓ : ℕ) : (renHQ n m ℓ : ℝ) = renH n m ℓ := by
  unfold renHQ renH renKQ renK
  split_ifs <;> push_cast <;> ring

theorem renAQ_cast (n m p : ℕ) : (renAQ n m p : ℝ) = renA n m p := by
  unfold renAQ renA
  push_cast
  simp only [renHQ_cast]

theorem renUQ_cast (n m i j : ℕ) : (renUQ n m i j : ℝ) = renU n m i j := by
  unfold renUQ renU
  split_ifs
  · push_cast
    rw [renAQ_cast, renAQ_cast]
  · push_cast
    rfl

theorem boxJQ_cast (n i j : ℕ) : (boxJQ n i j : ℝ) = boxJ n i j := by
  unfold boxJQ boxJ
  split_ifs <;> push_cast <;> rfl

theorem avgPlaceQ_cast (T : ℕ) (V : ℕ → ℕ → ℚ) (W : ℕ → ℕ → ℝ) (hVW : ∀ a b, (V a b : ℝ) = W a b)
    (i j : ℕ) : (avgPlaceQ T V i j : ℝ) = avgPlace T W i j := by
  unfold avgPlaceQ avgPlace
  push_cast
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  unfold placeQ place
  split_ifs
  · exact hVW _ _
  · push_cast
    rfl

theorem crossXQ_cast (n lo hi i j : ℕ) : (crossXQ n lo hi i j : ℝ) = crossX n lo hi i j := by
  unfold crossXQ crossX crossThetaQ crossTheta
  push_cast
  rw [renUQ_cast, renUQ_cast, avgPlaceQ_cast _ _ _ (boxJQ_cast (hi + 1)),
    avgPlaceQ_cast _ _ _ (renUQ_cast (hi + 1) (lo - 1))]

/-! ## Kernel check for `n ≤ 8` -/

/-- The short-run inequality for `crossXQ` in the `n`-box and the interval `[lo, hi]`. -/
def ShortOKQ (n lo hi : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, Nat.dist i j < lo → 0 ≤ crossXQ n lo hi i j

instance (n lo hi : ℕ) : Decidable (ShortOKQ n lo hi) :=
  inferInstanceAs (Decidable (∀ i < n, ∀ j < n, Nat.dist i j < lo → 0 ≤ crossXQ n lo hi i j))

set_option maxRecDepth 100000 in
/-- `crossXQ ≥ 0` on all short runs of all boxes `n ≤ 8`, checked by the kernel. -/
theorem shortOKQ_le_8 : ∀ n < 9, ∀ hi < n, ∀ lo < hi + 1, 1 ≤ lo → hi + 2 ≤ n →
    ShortOKQ n lo hi := by
  decide +kernel

/-- **The short-run inequality holds for all boxes of size `n ≤ 8`.** -/
theorem xShortNonneg_le_8 : ∀ n ≤ 8, ∀ lo hi, 1 ≤ lo → lo ≤ hi → hi + 2 ≤ n →
    XShortNonneg n lo hi := by
  intro n hn lo hi h1 h2 h3 i j hi' hj' hd
  rw [← crossXQ_cast]
  exact_mod_cast shortOKQ_le_8 n (by omega) hi (by omega) lo (by omega) h1 h3 i hi' j hj' hd

/-- The STU conjecture for `d ≤ 8` along the interval-uniformisation route (renewal squares and the
cross construction; no hook decompositions, no Kirwan convexity). -/
theorem stu_exists_le_8_of_unif {d : ℕ} (hd : d ≤ 8) (E : Fin d → ℝ) (hE : Monotone E)
    (β β' : ℝ) (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  stu_exists_of_shortNonneg (fun n hn => xShortNonneg_le_8 n (hn.trans hd)) E hE β β' hβ hβ'0
    hβ'β

end STUProof
