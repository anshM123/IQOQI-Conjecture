import STUProof.KirwanFree
import STUProof.HookDoubling
import STUProof.HookCert21
import STUProof.HookCert23
import STUProof.HookCert25
import STUProof.HookCert27
import STUProof.HookCert29
import STUProof.HookCert31
import STUProof.HookCert33
import STUProof.HookCert35
import STUProof.HookCert37
import STUProof.HookCert39

/-!
# Symmetrically thermalizing unitaries for `d ≤ 40` without Kirwan's theorem

The Hook Decomposition Lemma holds for every box size `n ≤ 40`:
* `n ≤ 20`: kernel-checked certificates (`hookDecomposition_le_20`);
* odd `n = 21, 23, …, 39`: kernel-checked certificates (`STUProof/HookCert{n}.lean`);
* even `n = 22, 24, …, 40`: the doubling lemma (`hookDecomposition_double`) applied to `n / 2 ≤ 20`.

More generally it holds for every `n = 2^k m` with `m ≤ 40`, i.e. for every box size whose odd
part is at most `39` (`hookDecomposition_two_pow_mul_le_40`). With `stu_exists_kirwanFree` this
proves the STU conjecture unconditionally in every local dimension `d ≤ 40` (`stu_exists_le_40`).
-/

open Matrix Finset
open scoped Kronecker

namespace STUProof

/-- **Hook Decomposition Lemma for all boxes of size at most 40**: certificates for `n ≤ 20` and
for odd `n ≤ 39`, doubling for even `22 ≤ n ≤ 40`. -/
theorem hookDecomposition_le_40 : ∀ n ≤ 40, HookDecomposition n := by
  intro n hn
  by_cases h20 : n ≤ 20
  · exact hookDecomposition_le_20 n h20
  have h21 : 21 ≤ n := by omega
  have hd : ∀ m ≤ 20, HookDecomposition (2 * m) :=
    fun m hm => hookDecomposition_double (hookDecomposition_le_20 m hm)
  interval_cases n
  · exact hookDecomposition_21
  · exact hd 11 (by norm_num)
  · exact hookDecomposition_23
  · exact hd 12 (by norm_num)
  · exact hookDecomposition_25
  · exact hd 13 (by norm_num)
  · exact hookDecomposition_27
  · exact hd 14 (by norm_num)
  · exact hookDecomposition_29
  · exact hd 15 (by norm_num)
  · exact hookDecomposition_31
  · exact hd 16 (by norm_num)
  · exact hookDecomposition_33
  · exact hd 17 (by norm_num)
  · exact hookDecomposition_35
  · exact hd 18 (by norm_num)
  · exact hookDecomposition_37
  · exact hd 19 (by norm_num)
  · exact hookDecomposition_39
  · exact hd 20 (by norm_num)

/-- **Hook Decomposition Lemma for every box size whose odd part is at most `39`**:
`HookDecomposition (2^k m)` for all `k` and all `m ≤ 40`. -/
theorem hookDecomposition_two_pow_mul_le_40 (k : ℕ) {m : ℕ} (hm : m ≤ 40) :
    HookDecomposition (2 ^ k * m) :=
  hookDecomposition_two_pow_mul (hookDecomposition_le_40 m hm) k

/-- **Unconditional theorem for `d ≤ 40`.** Symmetrically thermalizing unitaries exist in every
local dimension `d ≤ 40`: no Kirwan convexity and no Hook Decomposition hypothesis
(`hookDecomposition_le_40`: kernel-checked certificates and the doubling lemma). -/
theorem stu_exists_le_40 {d : ℕ} (hd : d ≤ 40) (E : Fin d → ℝ) (hE : Monotone E) (β β' : ℝ)
    (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' :=
  stu_exists_kirwanFree (fun n hn => hookDecomposition_le_40 n (hn.trans hd)) E hE β β' hβ hβ'0
    hβ'β

end STUProof
