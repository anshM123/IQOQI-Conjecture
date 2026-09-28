import STUProof.KirwanFreeHook
import STUProof.HookCertificates

/-!
# Symmetrically thermalizing unitaries without Kirwan's theorem

This file formalizes the Kirwan-free proof of P-STU3 (`iqoqi/programs/stu3/LOG.md`). The only
remaining hypothesis is the spectrum-independent Hook Decomposition Lemma `HookDecomposition n`
(`STUProof/KirwanFreeHook.lean`), for box sizes `n ≤ d`.

## Main results

* `stu_exists_kirwanFree (hH : ∀ n ≤ d, HookDecomposition n)`: the STU conjecture in dimension `d`.
* `stu_exists_of_hookDecomposition (hH : ∀ n, HookDecomposition n)`: all dimensions at once (the
  plug-in point for an all-`n` proof of the Hook Decomposition Lemma).
* `stu_exists_le_20`: **unconditional** for `d ≤ 20` (the hook decompositions of all boxes of
  size `n ≤ 20` are kernel-checked certificates, `STUProof/HookCertificates.lean`).

## Proof

Let `p = Gibbs(β)` (sorted, positive) and `w_k = min(p, p_k) / Z_k`, `Z_k = ∑_i min(p_i, p_k)`.

1. (Lemma T, `thermal_clip_weights`) `Gibbs(β') = ∑_k μ_k w_k` with `μ_k ≥ 0`, `∑ μ_k = 1`.
2. (fixed structure, `ReachTri.convex`) In the fixed tri-run structure (loop, upper and lower runs
   `{(i, i+s)}`), the reachable targets form a convex set.
3. (`wk_reach`) Every `w_k` is reachable in the tri-run structure. With `B = min(p, p_k)` and
   `c_m = p_m - p_{m+1}`, `p ⊗ p = B ⊗ B + ∑_{m<k, M} ω_{m,M} (Q_{min(m,M)} + U_{m,M})`
   (`wk_cell_identity`), all pieces non-increasing along every run (superposition). `B ⊗ B` is
   kept; each cross is replaced by the uniformisation of its hook interval (from the hook
   decompositions) in a box `[0, M']`, `M' ≥ k`: the big crosses (`M ≥ k`) in their own box, the
   other pieces in proportion to the leftover capacities (`leftM ≥ 0`, Hall slack). The rows are
   `w_k` (`wk_rows`) and every run is majorized (`wk_smaj`).
4. (`tri_reachable`) Schur–Horn on every run gives a real orthogonal `O`.
-/

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace STUProof

/-! ## Definitions of the construction -/

/-- `c_M = P_M - P_{M+1}`. -/
def cc (P : ℕ → ℝ) (M : ℕ) : ℝ := P M - P (M + 1)

/-- The clipped vector `B = min(P, P_k)`. -/
def clipB (P : ℕ → ℝ) (k i : ℕ) : ℝ := min (P i) (P k)

/-- Weight of the pair `(m, M)` in the decomposition of `P ⊗ P - B ⊗ B`. -/
def omg (P : ℕ → ℝ) (k m M : ℕ) : ℝ := cc P m * cc P M * (if k ≤ M then 1 else 1 / 2)

/-- Mass of the hook interval `[lo, hi]`: `∑_{a ∈ [lo, hi]} (2a+1)`. -/
def hmass (lo hi : ℕ) : ℝ := ∑ a ∈ Icc lo hi, (2 * (a : ℝ) + 1)

/-- Mass of the crosses placed in their own box `[0, M]` (for `M ≥ k`). -/
def bigM (P : ℕ → ℝ) (k M : ℕ) : ℝ := ∑ m ∈ range k, omg P k m M * hmass (M - m) M

/-- Total mass that box `[0, M]` (`M ≥ k`) must receive: `(1 - Z²)(M+1) c_M / Z`. -/
def aM (P : ℕ → ℝ) (d k M : ℕ) : ℝ :=
  (1 - clipZ P d k ^ 2) * (M + 1) * cc P M / clipZ P d k

/-- Leftover capacity of box `[0, M]`. -/
def leftM (P : ℕ → ℝ) (d k M : ℕ) : ℝ := aM P d k M - bigM P k M

/-- Total leftover capacity. -/
def Ltot (P : ℕ → ℝ) (d k : ℕ) : ℝ := ∑ M ∈ Ico k d, leftM P d k M

/-- Fraction of the flexible pieces sent to box `[0, M]`. -/
def fw (P : ℕ → ℝ) (d k M : ℕ) : ℝ := leftM P d k M / Ltot P d k

/-- A flexible piece (hook interval `[lo, hi]`) spread over the boxes `[0, M]`, `M ≥ k`. -/
def flexU (d : ℕ) (P : ℕ → ℝ) (k : ℕ) (X : ℕ → ℕ → ℕ → ℕ → ℝ) (lo hi i j : ℕ) : ℝ :=
  ∑ M ∈ Ico k d, fw P d k M * unif (M + 1) (X (M + 1)) lo hi i j

/-- The configuration replacing `Q_{min(m,M)} + U_{m,M}`. -/
def compG (d : ℕ) (P : ℕ → ℝ) (k : ℕ) (X : ℕ → ℕ → ℕ → ℕ → ℝ) (m M i j : ℕ) : ℝ :=
  (if k ≤ M then unif (M + 1) (X (M + 1)) (max m M - min m M) (max m M) i j
    else flexU d P k X (max m M - min m M) (max m M) i j) +
  flexU d P k X (min m M - min m M) (min m M) i j

/-- The configuration realizing `w_k` in the tri-run structure. -/
def wkConfig (d : ℕ) (P : ℕ → ℝ) (k : ℕ) (X : ℕ → ℕ → ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  clipB P k i * clipB P k j +
    ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M * compG d P k X m M i j

/-! ## Identities -/

section Identities

variable {d : ℕ} {P : ℕ → ℝ} {k : ℕ}
  (hanti : ∀ i j, i ≤ j → j < d → P j ≤ P i) (hpos : ∀ i < d, 0 < P i) (hPd : P d = 0)
  (hsum : ∑ i ∈ range d, P i = 1) (hk : k < d)

include hanti hpos hPd in
theorem cc_nonneg {M : ℕ} (hM : M < d) : 0 ≤ cc P M := by
  unfold cc
  rcases Nat.lt_or_ge (M + 1) d with h | h
  · linarith [hanti M (M + 1) (by omega) h]
  · rw [show M + 1 = d by omega, hPd]
    linarith [hpos M hM]

include hanti in
theorem clipB_anti {i j : ℕ} (hij : i ≤ j) (hj : j < d) : clipB P k j ≤ clipB P k i :=
  min_le_min_right _ (hanti i j hij hj)

include hpos in
theorem clipB_nonneg (hk : k < d) (i : ℕ) (hi : i < d) : 0 ≤ clipB P k i :=
  le_min (hpos i hi).le (hpos k hk).le

include hpos hk in
theorem clipZ_pos : 0 < clipZ P d k := by
  have : min (P k) (P k) ≤ clipZ P d k :=
    Finset.single_le_sum (f := fun j => min (P j) (P k))
      (fun j hj => le_min (hpos j (Finset.mem_range.1 hj)).le (hpos k hk).le)
      (Finset.mem_range.2 hk)
  rw [min_self] at this
  linarith [hpos k hk]

include hsum in
theorem clipZ_le_one : clipZ P d k ≤ 1 := by
  rw [← hsum]
  exact Finset.sum_le_sum (fun j _ => min_le_left _ _)

include hPd in
/-- Telescoping: `∑_{M ∈ [a, d)} c_M = P_a`. -/
theorem sum_cc_Ico {a : ℕ} (ha : a ≤ d) : ∑ M ∈ Ico a d, cc P M = P a := by
  have h : ∀ m, ∑ M ∈ range m, cc P M = P 0 - P m := by
    intro m
    unfold cc
    exact Finset.sum_range_sub' P m
  rw [Finset.sum_Ico_eq_sub _ ha, h, h, hPd]
  ring

include hPd in
theorem sum_cc_filter {r : ℕ} (hr : r < d) (a : ℕ) (ha : a ≤ d) :
    ∑ M ∈ Ico a d, (if r ≤ M then cc P M else 0) = P (max r a) := by
  rw [← Finset.sum_filter]
  have hf : (Ico a d).filter (fun M => r ≤ M) = Ico (max r a) d := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hf, sum_cc_Ico hPd (by omega)]

include hanti hPd hk in
theorem sum_cc_clipB {r : ℕ} (hr : r < d) :
    ∑ M ∈ Ico k d, (if r ≤ M then cc P M else 0) = clipB P k r := by
  rw [sum_cc_filter hPd hr k hk.le, clipB]
  rcases le_total r k with h | h
  · rw [max_eq_right h, min_eq_right (hanti r k h hk)]
  · rw [max_eq_left h, min_eq_left (hanti k r h hr)]

include hPd in
theorem P_eq_sum_cc {r : ℕ} (hr : r < d) :
    P r = ∑ M ∈ range d, (if r ≤ M then cc P M else 0) := by
  have h := sum_cc_filter hPd hr 0 (Nat.zero_le d)
  rw [max_eq_left (Nat.zero_le r), Nat.Ico_zero_eq_range] at h
  exact h.symm

end Identities

section Identities2

variable {d : ℕ} {P : ℕ → ℝ} {k : ℕ}
  (hanti : ∀ i j, i ≤ j → j < d → P j ≤ P i) (hpos : ∀ i < d, 0 < P i) (hPd : P d = 0)
  (hsum : ∑ i ∈ range d, P i = 1) (hk : k < d)

include hanti hPd hk in
/-- `Z = ∑_{M ≥ k} (M+1) c_M`. -/
theorem clipZ_eq : clipZ P d k = ∑ M ∈ Ico k d, ((M : ℝ) + 1) * cc P M := by
  show ∑ r ∈ range d, clipB P k r = _
  rw [Finset.sum_congr rfl (fun r hr => (sum_cc_clipB hanti hPd hk (Finset.mem_range.1 hr)).symm),
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  rw [Finset.mem_Ico] at hM
  rw [← ind_sum hM.2, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs <;> simp

theorem sum_cc_mul (K : ℕ) :
    ∑ m ∈ range K, cc P m * ((m : ℝ) + 1) = ∑ m ∈ range K, P m - K * P K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, cc]
    push_cast
    ring

include hanti hsum hk in
/-- `1 - Z = ∑_{m < k} (m+1) c_m`. -/
theorem one_sub_clipZ : 1 - clipZ P d k = ∑ m ∈ range k, cc P m * ((m : ℝ) + 1) := by
  rw [sum_cc_mul, ← hsum]
  unfold clipZ
  rw [← Finset.sum_sub_distrib, ← Finset.sum_range_add_sum_Ico _ hk.le]
  have h1 : ∑ i ∈ Ico k d, (P i - min (P i) (P k)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [min_eq_left (hanti k i hi.1 hi.2), sub_self]
  have h2 : ∑ i ∈ range k, (P i - min (P i) (P k)) = ∑ i ∈ range k, (P i - P k) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [min_eq_right (hanti i k hi.le hk)]
  rw [h1, h2, add_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

include hanti hpos hPd hk in
theorem sum_aM : ∑ M ∈ Ico k d, aM P d k M = 1 - clipZ P d k ^ 2 := by
  have hZ := clipZ_pos hpos hk
  have h : ∀ M, aM P d k M = (1 - clipZ P d k ^ 2) / clipZ P d k * (((M : ℝ) + 1) * cc P M) := by
    intro M
    unfold aM
    ring
  rw [Finset.sum_congr rfl (fun M _ => h M), ← Finset.mul_sum, ← clipZ_eq hanti hPd hk,
    div_mul_cancel₀ _ hZ.ne']

theorem crossInd_norm (m M i j : ℕ) : crossInd m M i j = crossInd (min m M) (max m M) i j := by
  rcases le_total m M with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, crossInd_comm]

theorem crossInd_pair (m M i j : ℕ) :
    crossInd (min m M) (min m M) i j + crossInd m M i j =
      (if i ≤ m then (1 : ℝ) else 0) * (if j ≤ M then 1 else 0) +
        (if i ≤ M then (1 : ℝ) else 0) * (if j ≤ m then 1 else 0) := by
  rw [crossInd_eq (min m M) (min m M), crossInd_eq m M, min_self]
  ring

include hanti hPd hk in
theorem sum_ind_cc_range_k {i : ℕ} (hi : i < d) :
    ∑ m ∈ range k, (if i ≤ m then cc P m else 0) = P i - clipB P k i := by
  rw [P_eq_sum_cc hPd hi, ← sum_cc_clipB hanti hPd hk hi,
    ← Finset.sum_range_add_sum_Ico _ hk.le]
  ring

include hanti hPd hk in
theorem sum_ind_cc_weighted {j : ℕ} (hj : j < d) :
    ∑ M ∈ range d, (if j ≤ M then cc P M else 0) * (1 + (if k ≤ M then 1 else 0)) =
      P j + clipB P k j := by
  have e : ∀ M, (if j ≤ M then cc P M else 0) * (1 + (if k ≤ M then (1 : ℝ) else 0)) =
      (if j ≤ M then cc P M else 0) + (if k ≤ M then (if j ≤ M then cc P M else 0) else 0) := by
    intro M
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun M _ => e M), Finset.sum_add_distrib, ← P_eq_sum_cc hPd hj,
    ← sum_cc_clipB hanti hPd hk hj, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 2
  ext M
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

include hanti hPd hk in
/-- **Decomposition of `P ⊗ P`**: `P_i P_j = B_i B_j + ∑_{m<k, M} ω_{m,M} (Q_{min(m,M)} + U_{m,M})`
at every cell. -/
theorem wk_cell_identity {i j : ℕ} (hi : i < d) (hj : j < d) :
    P i * P j = clipB P k i * clipB P k j + ∑ m ∈ range k, ∑ M ∈ range d,
      omg P k m M * (crossInd (min m M) (min m M) i j + crossInd m M i j) := by
  have key : ∑ m ∈ range k, ∑ M ∈ range d,
      omg P k m M * (crossInd (min m M) (min m M) i j + crossInd m M i j) =
      (1 / 2) * ((∑ m ∈ range k, (if i ≤ m then cc P m else 0)) *
          (∑ M ∈ range d, (if j ≤ M then cc P M else 0) * (1 + (if k ≤ M then 1 else 0))) +
        (∑ m ∈ range k, (if j ≤ m then cc P m else 0)) *
          (∑ M ∈ range d, (if i ≤ M then cc P M else 0) * (1 + (if k ≤ M then 1 else 0)))) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    rw [crossInd_pair]
    unfold omg
    split_ifs <;> ring
  rw [key, sum_ind_cc_range_k hanti hPd hk hi, sum_ind_cc_range_k hanti hPd hk hj,
    sum_ind_cc_weighted hanti hPd hk hi, sum_ind_cc_weighted hanti hPd hk hj]
  ring

include hanti hPd hsum hk in
/-- Total mass of the pieces of `P ⊗ P - B ⊗ B`. -/
theorem wk_mass : ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M *
    (hmass (min m M - min m M) (min m M) + hmass (max m M - min m M) (max m M)) =
      1 - clipZ P d k ^ 2 := by
  have hcells : ∀ m ∈ range k, ∀ M ∈ range d,
      hmass (min m M - min m M) (min m M) + hmass (max m M - min m M) (max m M) =
        ∑ x ∈ range d ×ˢ range d, (crossInd (min m M) (min m M) x.1 x.2 + crossInd m M x.1 x.2) := by
    intro m hm M hM
    rw [Finset.mem_range] at hm hM
    rw [Finset.sum_product, Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib),
      Finset.sum_add_distrib]
    unfold hmass
    rw [crossInd_sum le_rfl (by omega : min m M < d)]
    congr 1
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => crossInd_norm m M i j))]
    exact (crossInd_sum (min_le_max) (by omega : max m M < d)).symm
  have hZ : 1 - clipZ P d k ^ 2 = ∑ x ∈ range d ×ˢ range d,
      (P x.1 * P x.2 - clipB P k x.1 * clipB P k x.2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_product' (f := fun i j => P i * P j),
      Finset.sum_product' (f := fun i j => clipB P k i * clipB P k j), ← Finset.sum_mul_sum,
      ← Finset.sum_mul_sum, hsum]
    unfold clipZ clipB
    ring
  rw [hZ, Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun M hM => by
    rw [hcells m hm M hM, Finset.mul_sum]))]
  rw [Finset.sum_congr rfl (fun m _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
  rw [wk_cell_identity hanti hPd hk hx.1 hx.2]
  ring

include hanti hpos hPd hsum hk in
theorem bigM_le {M : ℕ} (hM : M ∈ Ico k d) :
    bigM P k M ≤ 2 * ((M : ℝ) + 1) * cc P M * (1 - clipZ P d k) := by
  rw [Finset.mem_Ico] at hM
  have hcM := cc_nonneg hanti hpos hPd hM.2
  rw [one_sub_clipZ hanti hsum hk, Finset.mul_sum]
  unfold bigM
  refine Finset.sum_le_sum (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  have hcm := cc_nonneg hanti hpos hPd (by omega : m < d)
  have hh : hmass (M - m) M ≤ ((m : ℝ) + 1) * (2 * M + 1) := by
    unfold hmass
    calc ∑ a ∈ Icc (M - m) M, (2 * (a : ℝ) + 1) ≤ ∑ _a ∈ Icc (M - m) M, (2 * (M : ℝ) + 1) :=
          Finset.sum_le_sum (fun a ha => by
            rw [Finset.mem_Icc] at ha
            have : (a : ℝ) ≤ M := by exact_mod_cast ha.2
            linarith)
      _ = ((m : ℝ) + 1) * (2 * M + 1) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          have : M + 1 - (M - m) = m + 1 := by omega
          rw [this]
          push_cast
          ring
  unfold omg
  rw [if_pos hM.1]
  have h1 : 0 ≤ cc P m * cc P M := mul_nonneg hcm hcM
  have h2 : hmass (M - m) M ≤ 2 * ((m : ℝ) + 1) * ((M : ℝ) + 1) := by nlinarith
  nlinarith

include hpos hk in
theorem aM_sub (M : ℕ) : aM P d k M - 2 * ((M : ℝ) + 1) * cc P M * (1 - clipZ P d k) =
    ((M : ℝ) + 1) * cc P M * (1 - clipZ P d k) ^ 2 / clipZ P d k := by
  have hZ := clipZ_pos hpos hk
  unfold aM
  field_simp
  ring

include hanti hpos hPd hsum hk in
/-- **Hall slack**: every box `[0, M]`, `M ≥ k`, has nonnegative leftover capacity. -/
theorem leftM_nonneg {M : ℕ} (hM : M ∈ Ico k d) : 0 ≤ leftM P d k M := by
  have hZ := clipZ_pos hpos hk
  have hcM := cc_nonneg hanti hpos hPd (Finset.mem_Ico.1 hM).2
  have h1 := bigM_le hanti hpos hPd hsum hk hM
  have h2 := aM_sub (d := d) (P := P) hpos hk M
  have h3 : 0 ≤ ((M : ℝ) + 1) * cc P M * (1 - clipZ P d k) ^ 2 / clipZ P d k := by positivity
  unfold leftM
  linarith

include hanti hpos hPd hsum hk in
theorem Ltot_nonneg : 0 ≤ Ltot P d k :=
  Finset.sum_nonneg (fun _ hM => leftM_nonneg hanti hpos hPd hsum hk hM)

include hanti hpos hPd hsum hk in
/-- If some `c_m` (`m < k`) is nonzero, the leftover capacity is positive. -/
theorem Ltot_pos {m : ℕ} (hm : m < k) (hcm : cc P m ≠ 0) : 0 < Ltot P d k := by
  have hZ := clipZ_pos hpos hk
  have hcm' : 0 < cc P m := lt_of_le_of_ne (cc_nonneg hanti hpos hPd (by omega)) (Ne.symm hcm)
  have hE : 0 < 1 - clipZ P d k := by
    rw [one_sub_clipZ hanti hsum hk]
    have h1 : cc P m * ((m : ℝ) + 1) ≤ ∑ m ∈ range k, cc P m * ((m : ℝ) + 1) :=
      Finset.single_le_sum (f := fun m => cc P m * ((m : ℝ) + 1))
        (fun m' hm' => mul_nonneg (cc_nonneg hanti hpos hPd
          (by rw [Finset.mem_range] at hm'; omega)) (by positivity)) (Finset.mem_range.2 hm)
    have h2 : 0 < cc P m * ((m : ℝ) + 1) := by positivity
    linarith
  have hlast : d - 1 ∈ Ico k d := Finset.mem_Ico.2 ⟨by omega, by omega⟩
  have hcl : cc P (d - 1) = P (d - 1) := by
    unfold cc
    rw [show d - 1 + 1 = d by omega, hPd, sub_zero]
  have hleft : 0 < leftM P d k (d - 1) := by
    have h1 := bigM_le hanti hpos hPd hsum hk hlast
    have h2 := aM_sub (d := d) (P := P) hpos hk (d - 1)
    have h3 : 0 < (((d - 1 : ℕ) : ℝ) + 1) * cc P (d - 1) * (1 - clipZ P d k) ^ 2 /
        clipZ P d k := by
      rw [hcl]
      have := hpos (d - 1) (by omega)
      positivity
    unfold leftM
    linarith
  calc 0 < leftM P d k (d - 1) := hleft
    _ ≤ Ltot P d k := Finset.single_le_sum (f := fun M => leftM P d k M)
        (fun M hM => leftM_nonneg hanti hpos hPd hsum hk hM) hlast

end Identities2

/-! ## The configuration realizing `w_k` -/

section Config

variable {d : ℕ} {P : ℕ → ℝ} {k : ℕ} {X : ℕ → ℕ → ℕ → ℕ → ℝ}
  (hanti : ∀ i j, i ≤ j → j < d → P j ≤ P i) (hpos : ∀ i < d, 0 < P i) (hPd : P d = 0)
  (hsum : ∑ i ∈ range d, P i = 1) (hk : k < d)
  (hX : ∀ n, n ≤ d → IsHookDecomposition n (X n))

include hanti hpos hPd hsum hk in
theorem fw_nonneg {M : ℕ} (hM : M ∈ Ico k d) : 0 ≤ fw P d k M :=
  div_nonneg (leftM_nonneg hanti hpos hPd hsum hk hM) (Ltot_nonneg hanti hpos hPd hsum hk)

theorem sum_fw (hL : 0 < Ltot P d k) : ∑ M ∈ Ico k d, fw P d k M = 1 := by
  unfold fw
  rw [← Finset.sum_div]
  exact div_self hL.ne'

include hanti hpos hPd hsum hk in
theorem fw_mul_Ltot {M : ℕ} (hM : M ∈ Ico k d) : fw P d k M * Ltot P d k = leftM P d k M := by
  unfold fw
  rcases eq_or_ne (Ltot P d k) 0 with h | h
  · have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun M hM => leftM_nonneg hanti hpos hPd hsum hk hM)).1 h M hM
    rw [h, h0, mul_zero]
  · exact div_mul_cancel₀ _ h

include hanti hpos hPd in
theorem omg_nonneg {m M : ℕ} (hm : m < d) (hM : M < d) : 0 ≤ omg P k m M := by
  unfold omg
  have := cc_nonneg hanti hpos hPd hm
  have := cc_nonneg hanti hpos hPd hM
  split_ifs <;> positivity

theorem flexU_symm (lo hi i j : ℕ) : flexU d P k X lo hi i j = flexU d P k X lo hi j i :=
  Finset.sum_congr rfl (fun M _ => by rw [unif_symm])

theorem compG_symm (m M i j : ℕ) : compG d P k X m M i j = compG d P k X m M j i := by
  unfold compG
  rw [flexU_symm, flexU_symm (i := i), unif_symm]

theorem wkConfig_symm (i j : ℕ) : wkConfig d P k X i j = wkConfig d P k X j i := by
  unfold wkConfig
  rw [mul_comm (clipB P k i)]
  congr 1
  exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun M _ => by rw [compG_symm]))

include hanti hpos hPd hsum hk hX in
/-- A flexible piece is majorized on every run by its cross. -/
theorem flex_smaj {s : ℕ} (hs : s < d) {u v : ℕ} (huv : u ≤ v) (hv : v < k)
    (hL : 0 < Ltot P d k) :
    SMaj (d - s) (fun i => flexU d P k X (v - u) v i (i + s))
      (fun i => crossInd u v i (i + s)) := by
  have each : ∀ M ∈ Ico k d, SMaj (d - s)
      (fun i => fw P d k M * unif (M + 1) (X (M + 1)) (v - u) v i (i + s))
      (fun i => fw P d k M * crossInd u v i (i + s)) := by
    intro M hM
    have hM' := Finset.mem_Ico.1 hM
    exact (unif_smaj (hX (M + 1) (by omega)) huv (by omega) (by omega) hs).smul
      (fw_nonneg hanti hpos hPd hsum hk hM)
  refine (SMaj.sum (Ico k d) each).congr (fun i _ => rfl) (fun i _ => ?_)
  rw [← Finset.sum_mul, sum_fw hL, one_mul]

include hanti hpos hPd hsum hk hX in
/-- The replacement of `Q_{min(m,M)} + U_{m,M}` is majorized on every run. -/
theorem comp_smaj {s : ℕ} (hs : s < d) {m M : ℕ} (hm : m < k) (hM : M < d)
    (hω : omg P k m M ≠ 0) :
    SMaj (d - s) (fun i => compG d P k X m M i (i + s))
      (fun i => crossInd (min m M) (min m M) i (i + s) + crossInd m M i (i + s)) := by
  have hcm : cc P m ≠ 0 := by
    intro h
    apply hω
    unfold omg
    rw [h, zero_mul, zero_mul]
  have hL := Ltot_pos hanti hpos hPd hsum hk hm hcm
  have hsq := flex_smaj hanti hpos hPd hsum hk hX hs (le_refl (min m M))
    (by omega : min m M < k) hL
  by_cases hkM : k ≤ M
  · have hmax : max m M = M := max_eq_right (by omega)
    have hbig : SMaj (d - s)
        (fun i => unif (M + 1) (X (M + 1)) (max m M - min m M) (max m M) i (i + s))
        (fun i => crossInd (min m M) (max m M) i (i + s)) :=
      unif_smaj (hX (M + 1) (by omega)) min_le_max (by omega) (by omega) hs
    refine (hbig.add hsq).congr (fun i _ => ?_) (fun i _ => ?_)
    · simp only [compG, if_pos hkM]
    · rw [← crossInd_norm, add_comm]
  · have hflex := flex_smaj hanti hpos hPd hsum hk hX hs (min_le_max (a := m) (b := M))
      (by omega : max m M < k) hL
    refine (hflex.add hsq).congr (fun i _ => ?_) (fun i _ => ?_)
    · simp only [compG, if_neg hkM]
    · rw [← crossInd_norm, add_comm]

include hanti hpos hPd hsum hk hX in
/-- **Majorization on every run** of the `w_k` configuration. -/
theorem wk_smaj {s : ℕ} (hs : s < d) :
    SMaj (d - s) (fun i => wkConfig d P k X i (i + s)) (fun i => P i * P (i + s)) := by
  have hB : SMaj (d - s) (fun i => clipB P k i * clipB P k (i + s))
      (fun i => clipB P k i * clipB P k (i + s)) := by
    apply smaj_self
    intro i j hij hj
    exact mul_le_mul (clipB_anti hanti hij (by omega)) (clipB_anti hanti (by omega) (by omega))
      (clipB_nonneg hpos hk _ (by omega)) (clipB_nonneg hpos hk _ (by omega))
  have hcomp : ∀ m ∈ range k, ∀ M ∈ range d, SMaj (d - s)
      (fun i => omg P k m M * compG d P k X m M i (i + s))
      (fun i => omg P k m M * (crossInd (min m M) (min m M) i (i + s) +
        crossInd m M i (i + s))) := by
    intro m hm M hM
    rw [Finset.mem_range] at hm hM
    by_cases hω : omg P k m M = 0
    · simp only [hω, zero_mul]
      exact SMaj.zero _
    · exact (comp_smaj hanti hpos hPd hsum hk hX hs hm hM hω).smul
        (omg_nonneg hanti hpos hPd (by omega) hM)
  refine (hB.add (SMaj.sum (range k) (fun m hm => SMaj.sum (range d)
    (fun M hM => hcomp m hm M hM)))).congr (fun i _ => rfl) (fun i hi => ?_)
  exact (wk_cell_identity hanti hPd hk (by omega) (by omega)).symm

include hk in
theorem swapBig (φ : ℕ → ℝ) :
    ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M *
      (if k ≤ M then φ M * hmass (max m M - min m M) (max m M) else 0) =
      ∑ M ∈ Ico k d, φ M * bigM P k M := by
  rw [Finset.sum_comm, ← Finset.sum_range_add_sum_Ico _ hk.le]
  have h0 : ∑ M ∈ range k, ∑ m ∈ range k, omg P k m M *
      (if k ≤ M then φ M * hmass (max m M - min m M) (max m M) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro M hM
    rw [Finset.mem_range] at hM
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg (by omega), mul_zero]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  rw [Finset.mem_Ico] at hM
  unfold bigM
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  rw [if_pos hM.1, max_eq_right (by omega : m ≤ M), min_eq_left (by omega : m ≤ M)]
  ring

include hanti hpos hPd hsum hk in
/-- The flexible mass equals the total leftover capacity. -/
theorem flex_mass : ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M *
    (hmass (min m M - min m M) (min m M) +
      (if k ≤ M then 0 else hmass (max m M - min m M) (max m M))) = Ltot P d k := by
  have h1 := wk_mass hanti hPd hsum hk
  have h2 := swapBig (d := d) (P := P) hk (fun _ => 1)
  have h3 := sum_aM hanti hpos hPd hk
  have hL : Ltot P d k = ∑ M ∈ Ico k d, aM P d k M - ∑ M ∈ Ico k d, bigM P k M := by
    unfold Ltot leftM
    rw [Finset.sum_sub_distrib]
  have hsplit : ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M *
      (hmass (min m M - min m M) (min m M) + hmass (max m M - min m M) (max m M)) =
      ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M *
        (hmass (min m M - min m M) (min m M) +
          (if k ≤ M then 0 else hmass (max m M - min m M) (max m M))) +
      ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M *
        (if k ≤ M then hmass (max m M - min m M) (max m M) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    split_ifs <;> ring
  simp only [one_mul] at h2
  rw [hsplit, h2] at h1
  linarith

include hanti hpos hPd hsum hk hX in
/-- **Rows** of the `w_k` configuration: `B / Z`. -/
theorem wk_rows {r : ℕ} (hr : r < d) :
    ∑ j ∈ range d, wkConfig d P k X r j = clipB P k r / clipZ P d k := by
  have hZ := clipZ_pos hpos hk
  set ρ : ℕ → ℝ := fun M => if r < M + 1 then 1 / ((M : ℝ) + 1) else 0 with hρ
  set F₀ := ∑ M ∈ Ico k d, fw P d k M * ρ M with hF₀
  have hrowU : ∀ n lo hi, hi < n → n ≤ d →
      ∑ j ∈ range d, unif n (X n) lo hi r j = if r < n then hmass lo hi / n else 0 :=
    fun n lo hi h1 h2 => unif_row (hX n h2) h1 r d h2
  have hrowF : ∀ lo hi, hi < k → ∑ j ∈ range d, flexU d P k X lo hi r j = hmass lo hi * F₀ := by
    intro lo hi hhi
    unfold flexU
    rw [Finset.sum_comm, hF₀, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M hM => ?_)
    rw [Finset.mem_Ico] at hM
    rw [← Finset.mul_sum, hrowU (M + 1) lo hi (by omega) (by omega), hρ]
    simp only
    split_ifs
    · push_cast
      ring
    · ring
  have hrowC : ∀ m ∈ range k, ∀ M ∈ range d, ∑ j ∈ range d, compG d P k X m M r j =
      (if k ≤ M then ρ M * hmass (max m M - min m M) (max m M)
        else hmass (max m M - min m M) (max m M) * F₀) +
      hmass (min m M - min m M) (min m M) * F₀ := by
    intro m hm M hM
    rw [Finset.mem_range] at hm hM
    unfold compG
    rw [Finset.sum_add_distrib, hrowF _ _ (by omega : min m M < k)]
    congr 1
    split_ifs with hkM
    · rw [hrowU (M + 1) _ _ (by omega : max m M < M + 1) (by omega), hρ]
      simp only
      split_ifs
      · push_cast
        ring
      · ring
    · rw [hrowF _ _ (by omega : max m M < k)]
  have hmain : ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M * ∑ j ∈ range d, compG d P k X m M r j =
      (1 - clipZ P d k ^ 2) / clipZ P d k * clipB P k r := by
    have e1 : ∀ m ∈ range k, ∀ M ∈ range d,
        omg P k m M * ∑ j ∈ range d, compG d P k X m M r j =
        omg P k m M * (if k ≤ M then ρ M * hmass (max m M - min m M) (max m M) else 0) +
        F₀ * (omg P k m M * (hmass (min m M - min m M) (min m M) +
          (if k ≤ M then 0 else hmass (max m M - min m M) (max m M)))) := by
      intro m hm M hM
      rw [hrowC m hm M hM]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun M hM => e1 m hm M hM))]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [swapBig hk ρ, flex_mass hanti hpos hPd hsum hk, hF₀, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    have e2 : ∀ M ∈ Ico k d, ρ M * bigM P k M + fw P d k M * ρ M * Ltot P d k =
        ρ M * aM P d k M := by
      intro M hM
      have h := fw_mul_Ltot hanti hpos hPd hsum hk hM
      unfold leftM at h
      linear_combination ρ M * h
    rw [Finset.sum_congr rfl e2, ← sum_cc_clipB hanti hPd hk hr, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M hM => ?_)
    rw [hρ]
    simp only
    unfold aM
    split_ifs with h1 h2 h2
    · field_simp
    · omega
    · omega
    · ring
  unfold wkConfig
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ j ∈ range d, ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M * compG d P k X m M r j =
      ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M * ∑ j ∈ range d, compG d P k X m M r j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    rw [Finset.mul_sum]
  rw [h2, hmain]
  show clipB P k r * clipZ P d k + (1 - clipZ P d k ^ 2) / clipZ P d k * clipB P k r =
    clipB P k r / clipZ P d k
  field_simp
  ring

include hanti hpos hPd hsum hk hX in
/-- **Every clipped point `w_k = min(P, P_k) / Z_k` is reachable in the tri-run structure.** -/
theorem wk_reach : ReachTri d P (fun i => clipB P k i / clipZ P d k) :=
  ⟨wkConfig d P k X, wkConfig_symm, fun _ hs => wk_smaj hanti hpos hPd hsum hk hX hs,
    fun _ hr => wk_rows hanti hpos hPd hsum hk hX hr⟩

end Config

/-! ## The main theorem -/

theorem ReachTri.congr_target {d : ℕ} {P q q' : ℕ → ℝ} (h : ReachTri d P q)
    (hq : ∀ r < d, q r = q' r) : ReachTri d P q' := by
  obtain ⟨F, h1, h2, h3⟩ := h
  exact ⟨F, h1, h2, fun r hr => (h3 r hr).trans (hq r hr)⟩

/-- A choice of hook decompositions for all box sizes `n ≤ d`. -/
theorem exists_hookData {d : ℕ} (hH : ∀ n ≤ d, HookDecomposition n) :
    ∃ X : ℕ → ℕ → ℕ → ℕ → ℝ, ∀ n, n ≤ d → IsHookDecomposition n (X n) := by
  have h : ∀ n, ∃ x : ℕ → ℕ → ℕ → ℝ, n ≤ d → IsHookDecomposition n x := by
    intro n
    by_cases hn : n ≤ d
    · obtain ⟨x, hx⟩ := hH n hn
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose X hX using h
  exact ⟨X, hX⟩

/-- **Thermal targets are reachable in the tri-run structure**, given hook decompositions of all
boxes of size at most `d`. -/
theorem gibbs_reachTri {d : ℕ} (hd : 0 < d) (hH : ∀ n ≤ d, HookDecomposition n)
    (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ} (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ReachTri d (extN (gibbs E β)) (extN (gibbs E β')) := by
  obtain ⟨X, hX⟩ := exists_hookData hH
  set p := gibbs E β with hp
  set P := extN p with hP
  have hpA : Antitone p := gibbs_antitone E hE hβ.le
  have hanti : ∀ i j, i ≤ j → j < d → P j ≤ P i := by
    intro i j hij hj
    rw [hP, extN_lt p hj, extN_lt p (lt_of_le_of_lt hij hj)]
    exact hpA (Fin.mk_le_mk.2 hij)
  have hpos : ∀ i < d, 0 < P i := by
    intro i hi
    rw [hP, extN_lt p hi]
    exact gibbs_pos hd E β _
  have hPd : P d = 0 := by
    rw [hP]
    unfold extN
    rw [dif_neg (lt_irrefl d)]
  have hsum : ∑ i ∈ range d, P i = 1 := by
    rw [hP, sum_extN]
    exact gibbs_sum hd E β
  obtain ⟨μ, hμ0, hμ1, hμq⟩ := thermal_clip_weights hd E hE hβ h0 h1
  have hreach : ∀ k < d, ReachTri d P (fun i => clipB P k i / clipZ P d k) :=
    fun k hk => wk_reach hanti hpos hPd hsum hk hX
  refine (ReachTri.convex hμ0 hμ1 hreach).congr_target (fun r hr => ?_)
  exact (hμq r hr).symm

/-- **Symmetrically thermalizing unitaries exist in every local dimension, without Kirwan's
theorem** (conjecture of arXiv:1904.07942), assuming the spectrum-independent Hook Decomposition
Lemma for all box sizes `n ≤ d`.

For energies `E_0 ≤ … ≤ E_{d-1}`, `β > 0` and `0 ≤ β' ≤ β` there is a unitary `U` on
`ℂ^d ⊗ ℂ^d` (in fact a real orthogonal one) such that both marginals of `U (τ_β ⊗ τ_β) U†` equal
`τ_{β'}`. -/
theorem stu_exists_kirwanFree {d : ℕ} (hH : ∀ n ≤ d, HookDecomposition n) (E : Fin d → ℝ)
    (hE : Monotone E) (β β' : ℝ) (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, one_mem _, ?_, ?_⟩ <;> ext i <;> exact i.elim0
  obtain ⟨O, hO, hB, hA⟩ := (gibbs_reachTri hd hH E hE hβ hβ'0 hβ'β).orthogonal
  refine ⟨O.map Complex.ofRealHom, map_ofReal_mem_unitaryGroup hO, ?_, ?_⟩
  · rw [gibbsState_kronecker, conj_map_ofReal, partialTraceB_map_ofReal, hB,
      Matrix.diagonal_map (map_zero _)]
    rfl
  · rw [gibbsState_kronecker, conj_map_ofReal, partialTraceA_map_ofReal, hA,
      Matrix.diagonal_map (map_zero _)]
    rfl

/-- `stu_exists_kirwanFree` for all local dimensions at once, from the Hook Decomposition Lemma for
all box sizes (the form in which an all-`n` proof of `HookDecomposition` plugs in). -/
theorem stu_exists_of_hookDecomposition (hH : ∀ n, HookDecomposition n) :
    ∀ (d : ℕ) (E : Fin d → ℝ), Monotone E → ∀ β β' : ℝ, 0 < β → 0 ≤ β' → β' ≤ β →
      ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
        partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
        partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  fun _ E hE β β' hβ h0 h1 => stu_exists_kirwanFree (fun n _ => hH n) E hE β β' hβ h0 h1

/-- **Unconditional theorem for `d ≤ 20`.** Symmetrically thermalizing unitaries exist in every
local dimension `d ≤ 20`: no Kirwan convexity and no Hook Decomposition hypothesis (the hook
decompositions of all boxes of size `n ≤ 20` are kernel-checked certificates,
`hookDecomposition_le_20`). -/
theorem stu_exists_le_20 {d : ℕ} (hd : d ≤ 20) (E : Fin d → ℝ) (hE : Monotone E) (β β' : ℝ)
    (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  stu_exists_kirwanFree (fun n hn => hookDecomposition_le_20 n (hn.trans hd)) E hE β β' hβ hβ'0
    hβ'β

end STUProof
