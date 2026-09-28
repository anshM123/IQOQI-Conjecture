import STUProof.KirwanFreeHook

/-!
# Interval uniformisations

The Kirwan-free construction (`STUProof/KirwanFree.lean`) uses a hook decomposition of the
`n`-box only through the uniformisations `unif n x lo hi` of hook intervals `[lo, hi]`, and only
through the following properties (P-UNIF, `iqoqi/programs/unif/LOG.md`):
* symmetric, with entries in `[0, 1]`, zero off the box;
* the run `s` has total `#{a ∈ [lo, hi] : s ≤ a}`;
* every row of the box has total `∑_{a ∈ [lo, hi]} (2a+1) / n`.

`IsIntervalUnif n lo hi u` states these properties, and `IntervalUnifAll n` asks for such a `u`
for every interval `[lo, hi]` of the `n`-box, independently. A hook decomposition gives
`IntervalUnifAll n` (`intervalUnifAll_of_hookDecomposition`). The majorization of runs used by the
construction holds for every interval uniformisation (`IsIntervalUnif.smaj`).
-/

open Finset

noncomputable section

namespace STUProof

/-- An *interval uniformisation* of `[lo, hi]` in the `n`-box. -/
structure IsIntervalUnif (n lo hi : ℕ) (u : ℕ → ℕ → ℝ) : Prop where
  symm : ∀ i j, u i j = u j i
  nonneg : ∀ i j, 0 ≤ u i j
  le_one : ∀ i j, u i j ≤ 1
  zero : ∀ i j, n ≤ i → u i j = 0
  run : ∀ s, ∑ i ∈ range n, u i (i + s) = (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ)
  row : ∀ r < n, ∑ j ∈ range n, u r j = (∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1)) / n

/-- Interval uniformisations of all intervals of the `n`-box. -/
def IntervalUnifAll (n : ℕ) : Prop :=
  ∀ lo hi, lo ≤ hi → hi < n → ∃ u, IsIntervalUnif n lo hi u

namespace IsIntervalUnif

variable {n lo hi : ℕ} {u : ℕ → ℕ → ℝ}

theorem zero' (h : IsIntervalUnif n lo hi u) (i j : ℕ) (hj : n ≤ j) : u i j = 0 := by
  rw [h.symm]
  exact h.zero j i hj

/-- Run sums over any range `ℓ ≥ n - s`. -/
theorem run' (h : IsIntervalUnif n lo hi u) (s ℓ : ℕ) (hℓ : n - s ≤ ℓ) :
    ∑ i ∈ range ℓ, u i (i + s) = (((Icc lo hi).filter (fun a => s ≤ a)).card : ℝ) := by
  rw [← h.run s]
  have e : ∀ L, n - s ≤ L → ∑ i ∈ range L, u i (i + s) = ∑ i ∈ range (n - s), u i (i + s) := by
    intro L hL
    rw [← Finset.sum_range_add_sum_Ico _ hL]
    rw [Finset.sum_eq_zero (s := Ico (n - s) L) (fun i hi => h.zero' i (i + s)
      (by rw [Finset.mem_Ico] at hi; omega)), add_zero]
  rw [e ℓ hℓ, e n (Nat.sub_le n s)]

/-- Row sums over any range `ℓ ≥ n`. -/
theorem row' (h : IsIntervalUnif n lo hi u) (r ℓ : ℕ) (hℓ : n ≤ ℓ) :
    ∑ j ∈ range ℓ, u r j =
      if r < n then (∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1)) / n else 0 := by
  split_ifs with hr
  · rw [← h.row r hr, ← Finset.sum_range_add_sum_Ico _ hℓ]
    rw [Finset.sum_eq_zero (s := Ico n ℓ) (fun j hj => h.zero' r j
      (by rw [Finset.mem_Ico] at hj; omega)), add_zero]
  · exact Finset.sum_eq_zero (fun j _ => h.zero r j (by omega))

/-- **Majorization on every run** by the cross `C(v', v)` with arm interval `[v - v', v]`. -/
theorem smaj {v' v d : ℕ} (h : IsIntervalUnif n (v - v') v u) (hv : v' ≤ v) (hvn : v < n)
    (hnd : n ≤ d) {s : ℕ} (hs : s < d) :
    SMaj (d - s) (fun i => u i (i + s)) (fun i => crossInd v' v i (i + s)) := by
  set N := if s ≤ v then min v' (v - s) + 1 else 0 with hN
  have hNle : N ≤ d - s := by
    rw [hN]
    split_ifs <;> omega
  have hm := smaj_zeroOne hNle (x := fun i => u i (i + s))
    (fun i _ => h.nonneg _ _) (fun i _ => h.le_one _ _)
    (by rw [h.run' s (d - s) (by omega), card_filter_Icc_hook hv s])
  refine hm.congr (fun i _ => rfl) (fun i _ => ?_)
  rw [crossInd_run hv]

end IsIntervalUnif

/-- The uniformisation of a hook interval of a hook decomposition is an interval
uniformisation. -/
theorem isIntervalUnif_unif {n : ℕ} {x : ℕ → ℕ → ℕ → ℝ} (hx : IsHookDecomposition n x)
    {lo hi : ℕ} (hhi : hi < n) : IsIntervalUnif n lo hi (unif n x lo hi) :=
  { symm := fun i j => unif_symm lo hi i j
    nonneg := fun i j => unif_nonneg hx hhi i j
    le_one := fun i j => unif_le_one hx hhi i j
    zero := fun i j hi' => by
      unfold unif
      refine Finset.sum_eq_zero (fun a _ => ?_)
      simp only [hookCell]
      rw [if_neg (by omega)]
    run := fun s => unif_run hx hhi s n (Nat.sub_le n s)
    row := fun r hr => by
      rw [unif_row hx hhi r n le_rfl, if_pos hr] }

/-- A hook decomposition gives interval uniformisations of all intervals. -/
theorem intervalUnifAll_of_hookDecomposition {n : ℕ} (h : HookDecomposition n) :
    IntervalUnifAll n := by
  obtain ⟨x, hx⟩ := h
  exact fun lo hi _ hhi => ⟨_, isIntervalUnif_unif hx hhi⟩

/-! ## Counting helpers -/

/-- The run total of `[lo, hi]`: `#{a ∈ [lo, hi] : s ≤ a} = hi + 1 - max lo s`. -/
theorem card_filter_Icc_le (lo hi s : ℕ) :
    ((Icc lo hi).filter (fun a => s ≤ a)).card = hi + 1 - max lo s := by
  have hf : (Icc lo hi).filter (fun a => s ≤ a) = Icc (max lo s) hi := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hf, Nat.card_Icc]

/-- The hook mass `∑_{a ∈ [lo, hi]} (2a+1) = (hi+1)² - lo²` (for `lo ≤ hi + 1`). -/
theorem sum_Icc_odd {lo hi : ℕ} (h : lo ≤ hi + 1) :
    ∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1) = ((hi : ℝ) + 1) ^ 2 - (lo : ℝ) ^ 2 := by
  have hsq : ∀ m, ∑ a ∈ range m, (2 * (a : ℝ) + 1) = (m : ℝ) ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ h, hsq, hsq]
  push_cast
  ring

end STUProof
