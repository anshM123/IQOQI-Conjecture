import STUProof.KirwanFree
import STUProof.IntervalUnif

/-!
# The Kirwan-free proof from interval uniformisations

This is the construction of `STUProof/KirwanFree.lean` with the hook decompositions replaced by a
family `U n lo hi` of interval uniformisations (`STUProof/IntervalUnif.lean`): the configuration
realizing `w_k` uses `U (M + 1) lo hi` wherever `KirwanFree.lean` uses `unif (M + 1) (X (M + 1)) lo hi`.
All lemmas of `KirwanFree.lean` that do not involve the hook data are reused.

## Main result

* `stu_exists_of_intervalUnif (hU : ∀ n ≤ d, IntervalUnifAll n)`: the STU conjecture in dimension
  `d`, assuming interval uniformisations of all intervals of all boxes of size `n ≤ d`.
-/

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace STUProof

/-! ## The configuration realizing `w_k` -/

/-- A flexible piece (interval `[lo, hi]`) spread over the boxes `[0, M]`, `M ≥ k`. -/
def flexUU (d : ℕ) (P : ℕ → ℝ) (k : ℕ) (U : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (lo hi i j : ℕ) : ℝ :=
  ∑ M ∈ Ico k d, fw P d k M * U (M + 1) lo hi i j

/-- The configuration replacing `Q_{min(m,M)} + U_{m,M}`. -/
def compGU (d : ℕ) (P : ℕ → ℝ) (k : ℕ) (U : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (m M i j : ℕ) : ℝ :=
  (if k ≤ M then U (M + 1) (max m M - min m M) (max m M) i j
    else flexUU d P k U (max m M - min m M) (max m M) i j) +
  flexUU d P k U (min m M - min m M) (min m M) i j

/-- The configuration realizing `w_k` in the tri-run structure. -/
def wkConfigU (d : ℕ) (P : ℕ → ℝ) (k : ℕ) (U : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  clipB P k i * clipB P k j +
    ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M * compGU d P k U m M i j

section ConfigU

variable {d : ℕ} {P : ℕ → ℝ} {k : ℕ} {U : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ}
  (hanti : ∀ i j, i ≤ j → j < d → P j ≤ P i) (hpos : ∀ i < d, 0 < P i) (hPd : P d = 0)
  (hsum : ∑ i ∈ range d, P i = 1) (hk : k < d)
  (hU : ∀ n, n ≤ d → ∀ lo hi, lo ≤ hi → hi < n → IsIntervalUnif n lo hi (U n lo hi))

include hU in
theorem flexUU_symm {lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi < k) (i j : ℕ) :
    flexUU d P k U lo hi i j = flexUU d P k U lo hi j i :=
  Finset.sum_congr rfl (fun M hM => by
    rw [Finset.mem_Ico] at hM
    rw [(hU (M + 1) (by omega) lo hi hlo (by omega)).symm i j])

include hU in
theorem compGU_symm {m M : ℕ} (hm : m < k) (hM : M < d) (i j : ℕ) :
    compGU d P k U m M i j = compGU d P k U m M j i := by
  unfold compGU
  rw [flexUU_symm hU (Nat.sub_le _ _) (by omega : min m M < k) i j]
  congr 1
  split_ifs with hkM
  · exact (hU (M + 1) (by omega) _ _ (Nat.sub_le _ _) (by omega)).symm i j
  · exact flexUU_symm hU (Nat.sub_le _ _) (by omega) i j

include hU in
theorem wkConfigU_symm (i j : ℕ) : wkConfigU d P k U i j = wkConfigU d P k U j i := by
  unfold wkConfigU
  rw [mul_comm (clipB P k i)]
  congr 1
  refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun M hM => ?_))
  rw [Finset.mem_range] at hm hM
  rw [compGU_symm hU hm hM]

include hanti hpos hPd hsum hk hU in
/-- A flexible piece is majorized on every run by its cross. -/
theorem flexUU_smaj {s : ℕ} (hs : s < d) {u v : ℕ} (huv : u ≤ v) (hv : v < k)
    (hL : 0 < Ltot P d k) :
    SMaj (d - s) (fun i => flexUU d P k U (v - u) v i (i + s))
      (fun i => crossInd u v i (i + s)) := by
  have each : ∀ M ∈ Ico k d, SMaj (d - s)
      (fun i => fw P d k M * U (M + 1) (v - u) v i (i + s))
      (fun i => fw P d k M * crossInd u v i (i + s)) := by
    intro M hM
    have hM' := Finset.mem_Ico.1 hM
    exact ((hU (M + 1) (by omega) (v - u) v (Nat.sub_le v u) (by omega)).smaj huv (by omega)
      (by omega) hs).smul (fw_nonneg hanti hpos hPd hsum hk hM)
  refine (SMaj.sum (Ico k d) each).congr (fun i _ => rfl) (fun i _ => ?_)
  rw [← Finset.sum_mul, sum_fw hL, one_mul]

include hanti hpos hPd hsum hk hU in
/-- The replacement of `Q_{min(m,M)} + U_{m,M}` is majorized on every run. -/
theorem compGU_smaj {s : ℕ} (hs : s < d) {m M : ℕ} (hm : m < k) (hM : M < d)
    (hω : omg P k m M ≠ 0) :
    SMaj (d - s) (fun i => compGU d P k U m M i (i + s))
      (fun i => crossInd (min m M) (min m M) i (i + s) + crossInd m M i (i + s)) := by
  have hcm : cc P m ≠ 0 := by
    intro h
    apply hω
    unfold omg
    rw [h, zero_mul, zero_mul]
  have hL := Ltot_pos hanti hpos hPd hsum hk hm hcm
  have hsq := flexUU_smaj hanti hpos hPd hsum hk hU hs (le_refl (min m M))
    (by omega : min m M < k) hL
  by_cases hkM : k ≤ M
  · have hbig : SMaj (d - s)
        (fun i => U (M + 1) (max m M - min m M) (max m M) i (i + s))
        (fun i => crossInd (min m M) (max m M) i (i + s)) :=
      (hU (M + 1) (by omega) _ _ (Nat.sub_le _ _) (by omega)).smaj min_le_max (by omega)
        (by omega) hs
    refine (hbig.add hsq).congr (fun i _ => ?_) (fun i _ => ?_)
    · simp only [compGU, if_pos hkM]
    · rw [← crossInd_norm, add_comm]
  · have hflex := flexUU_smaj hanti hpos hPd hsum hk hU hs (min_le_max (a := m) (b := M))
      (by omega : max m M < k) hL
    refine (hflex.add hsq).congr (fun i _ => ?_) (fun i _ => ?_)
    · simp only [compGU, if_neg hkM]
    · rw [← crossInd_norm, add_comm]

include hanti hpos hPd hsum hk hU in
/-- **Majorization on every run** of the `w_k` configuration. -/
theorem wkU_smaj {s : ℕ} (hs : s < d) :
    SMaj (d - s) (fun i => wkConfigU d P k U i (i + s)) (fun i => P i * P (i + s)) := by
  have hB : SMaj (d - s) (fun i => clipB P k i * clipB P k (i + s))
      (fun i => clipB P k i * clipB P k (i + s)) := by
    apply smaj_self
    intro i j hij hj
    exact mul_le_mul (clipB_anti hanti hij (by omega)) (clipB_anti hanti (by omega) (by omega))
      (clipB_nonneg hpos hk _ (by omega)) (clipB_nonneg hpos hk _ (by omega))
  have hcomp : ∀ m ∈ range k, ∀ M ∈ range d, SMaj (d - s)
      (fun i => omg P k m M * compGU d P k U m M i (i + s))
      (fun i => omg P k m M * (crossInd (min m M) (min m M) i (i + s) +
        crossInd m M i (i + s))) := by
    intro m hm M hM
    rw [Finset.mem_range] at hm hM
    by_cases hω : omg P k m M = 0
    · simp only [hω, zero_mul]
      exact SMaj.zero _
    · exact (compGU_smaj hanti hpos hPd hsum hk hU hs hm hM hω).smul
        (omg_nonneg hanti hpos hPd (by omega) hM)
  refine (hB.add (SMaj.sum (range k) (fun m hm => SMaj.sum (range d)
    (fun M hM => hcomp m hm M hM)))).congr (fun i _ => rfl) (fun i hi => ?_)
  exact (wk_cell_identity hanti hPd hk (by omega) (by omega)).symm

include hanti hpos hPd hsum hk hU in
/-- **Rows** of the `w_k` configuration: `B / Z`. -/
theorem wkU_rows {r : ℕ} (hr : r < d) :
    ∑ j ∈ range d, wkConfigU d P k U r j = clipB P k r / clipZ P d k := by
  have hZ := clipZ_pos hpos hk
  set ρ : ℕ → ℝ := fun M => if r < M + 1 then 1 / ((M : ℝ) + 1) else 0 with hρ
  set F₀ := ∑ M ∈ Ico k d, fw P d k M * ρ M with hF₀
  have hrowU : ∀ n lo hi, lo ≤ hi → hi < n → n ≤ d →
      ∑ j ∈ range d, U n lo hi r j = if r < n then hmass lo hi / n else 0 :=
    fun n lo hi h0 h1 h2 => (hU n h2 lo hi h0 h1).row' r d h2
  have hrowF : ∀ lo hi, lo ≤ hi → hi < k →
      ∑ j ∈ range d, flexUU d P k U lo hi r j = hmass lo hi * F₀ := by
    intro lo hi hlo hhi
    unfold flexUU
    rw [Finset.sum_comm, hF₀, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M hM => ?_)
    rw [Finset.mem_Ico] at hM
    rw [← Finset.mul_sum, hrowU (M + 1) lo hi hlo (by omega) (by omega), hρ]
    simp only
    split_ifs
    · push_cast
      ring
    · ring
  have hrowC : ∀ m ∈ range k, ∀ M ∈ range d, ∑ j ∈ range d, compGU d P k U m M r j =
      (if k ≤ M then ρ M * hmass (max m M - min m M) (max m M)
        else hmass (max m M - min m M) (max m M) * F₀) +
      hmass (min m M - min m M) (min m M) * F₀ := by
    intro m hm M hM
    rw [Finset.mem_range] at hm hM
    unfold compGU
    rw [Finset.sum_add_distrib, hrowF _ _ (Nat.sub_le _ _) (by omega : min m M < k)]
    congr 1
    split_ifs with hkM
    · rw [hrowU (M + 1) _ _ (Nat.sub_le _ _) (by omega : max m M < M + 1) (by omega), hρ]
      simp only
      split_ifs
      · push_cast
        ring
      · ring
    · rw [hrowF _ _ (Nat.sub_le _ _) (by omega : max m M < k)]
  have hmain : ∑ m ∈ range k, ∑ M ∈ range d,
      omg P k m M * ∑ j ∈ range d, compGU d P k U m M r j =
      (1 - clipZ P d k ^ 2) / clipZ P d k * clipB P k r := by
    have e1 : ∀ m ∈ range k, ∀ M ∈ range d,
        omg P k m M * ∑ j ∈ range d, compGU d P k U m M r j =
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
  unfold wkConfigU
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ j ∈ range d, ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M * compGU d P k U m M r j =
      ∑ m ∈ range k, ∑ M ∈ range d, omg P k m M * ∑ j ∈ range d, compGU d P k U m M r j := by
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

include hanti hpos hPd hsum hk hU in
/-- **Every clipped point `w_k = min(P, P_k) / Z_k` is reachable in the tri-run structure.** -/
theorem wkU_reach : ReachTri d P (fun i => clipB P k i / clipZ P d k) :=
  ⟨wkConfigU d P k U, wkConfigU_symm hU, fun _ hs => wkU_smaj hanti hpos hPd hsum hk hU hs,
    fun _ hr => wkU_rows hanti hpos hPd hsum hk hU hr⟩

end ConfigU

/-! ## The main theorem -/

/-- A choice of interval uniformisations for all intervals of all boxes of size `n ≤ d`. -/
theorem exists_unifData {d : ℕ} (hU : ∀ n ≤ d, IntervalUnifAll n) :
    ∃ U : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ, ∀ n, n ≤ d → ∀ lo hi, lo ≤ hi → hi < n →
      IsIntervalUnif n lo hi (U n lo hi) := by
  have h : ∀ n lo hi, ∃ u : ℕ → ℕ → ℝ, n ≤ d → lo ≤ hi → hi < n → IsIntervalUnif n lo hi u := by
    intro n lo hi
    by_cases hn : n ≤ d ∧ lo ≤ hi ∧ hi < n
    · obtain ⟨u, hu⟩ := hU n hn.1 lo hi hn.2.1 hn.2.2
      exact ⟨u, fun _ _ _ => hu⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hn⟩
  choose U hU' using h
  exact ⟨U, fun n hn lo hi h1 h2 => hU' n lo hi hn h1 h2⟩

/-- **Thermal targets are reachable in the tri-run structure**, given interval uniformisations for
all boxes of size at most `d`. -/
theorem gibbs_reachTri_of_intervalUnif {d : ℕ} (hd : 0 < d) (hU : ∀ n ≤ d, IntervalUnifAll n)
    (E : Fin d → ℝ) (hE : Monotone E) {β β' : ℝ} (hβ : 0 < β) (h0 : 0 ≤ β') (h1 : β' ≤ β) :
    ReachTri d (extN (gibbs E β)) (extN (gibbs E β')) := by
  obtain ⟨U, hU'⟩ := exists_unifData hU
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
    fun k hk => wkU_reach hanti hpos hPd hsum hk hU'
  refine (ReachTri.convex hμ0 hμ1 hreach).congr_target (fun r hr => ?_)
  exact (hμq r hr).symm

/-- **Symmetrically thermalizing unitaries exist in every local dimension `d`, without Kirwan's
theorem**, assuming interval uniformisations (`IntervalUnifAll n`) for all box sizes `n ≤ d`. -/
theorem stu_exists_of_intervalUnif {d : ℕ} (hU : ∀ n ≤ d, IntervalUnifAll n) (E : Fin d → ℝ)
    (hE : Monotone E) (β β' : ℝ) (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, one_mem _, ?_, ?_⟩ <;> ext i <;> exact i.elim0
  obtain ⟨O, hO, hB, hA⟩ := (gibbs_reachTri_of_intervalUnif hd hU E hE hβ hβ'0 hβ'β).orthogonal
  refine ⟨O.map Complex.ofRealHom, map_ofReal_mem_unitaryGroup hO, ?_, ?_⟩
  · rw [gibbsState_kronecker, conj_map_ofReal, partialTraceB_map_ofReal, hB,
      Matrix.diagonal_map (map_zero _)]
    rfl
  · rw [gibbsState_kronecker, conj_map_ofReal, partialTraceA_map_ofReal, hA,
      Matrix.diagonal_map (map_zero _)]
    rfl

end STUProof
