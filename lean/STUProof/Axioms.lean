import STUProof.STU
import STUProof.KirwanFree
import STUProof.KirwanFree40
import STUProof.ShortNonnegSmall

/-! Axiom check for the main results (run after building the other files, see `check.sh`). -/

-- Kirwan route (hypothesis `KirwanSymmetricConvexity d`)
#print axioms STUProof.schurHorn
#print axioms STUProof.exists_constr
#print axioms STUProof.vk_reachable
#print axioms STUProof.lemma5
#print axioms STUProof.gibbs_mem_convexHull
#print axioms STUProof.vk_mem_symMarginalSpectra
#print axioms STUProof.symMarginalSpectra_eq
#print axioms STUProof.symMarginalSpectra_eq_charpoly
#print axioms STUProof.stu_of_mem_symMarginalSpectra
#print axioms STUProof.stu_exists
#print axioms STUProof.stu_exists_all

-- Kirwan-free route (hypothesis `HookDecomposition n`, `n ≤ d`)
#print axioms STUProof.lc_reachable
#print axioms STUProof.tri_reachable
#print axioms STUProof.ReachTri.convex
#print axioms STUProof.lemmaT
#print axioms STUProof.thermal_clip_weights
#print axioms STUProof.unif_smaj
#print axioms STUProof.wk_cell_identity
#print axioms STUProof.leftM_nonneg
#print axioms STUProof.wk_reach
#print axioms STUProof.gibbs_reachTri
#print axioms STUProof.stu_exists_kirwanFree
#print axioms STUProof.stu_exists_of_hookDecomposition

-- unconditional for `d ≤ 20` (kernel-checked hook decompositions)
#print axioms STUProof.hookDecomposition_le_20
#print axioms STUProof.stu_exists_le_20

-- doubling lemma: `HookDecomposition M → HookDecomposition (2 * M)`
#print axioms STUProof.IsHookCells.double
#print axioms STUProof.hookDecomposition_double
#print axioms STUProof.hookDecomposition_two_pow_mul
#print axioms STUProof.hookDecomposition_pow2

-- unconditional for `d ≤ 40` (certificates for odd `n ≤ 39`, doubling for even `n`)
#print axioms STUProof.hookDecomposition_39
#print axioms STUProof.hookDecomposition_le_40
#print axioms STUProof.hookDecomposition_two_pow_mul_le_40
#print axioms STUProof.stu_exists_le_40

-- interval uniformisations (hypothesis `IntervalUnifAll n`, `n ≤ d`)
#print axioms STUProof.intervalUnifAll_of_hookDecomposition
#print axioms STUProof.stu_exists_of_intervalUnif

-- explicit interval uniformisations: renewal square, `J`, complement, cross construction
#print axioms STUProof.isIntervalUnif_renU
#print axioms STUProof.isIntervalUnif_boxJ
#print axioms STUProof.IsIntervalUnif.compl
#print axioms STUProof.isIntervalUnif_crossX

-- all dimensions from the single inequality `XShortNonneg`
#print axioms STUProof.intervalUnifAll_of_shortNonneg
#print axioms STUProof.stu_exists_of_shortNonneg
#print axioms STUProof.stu_exists_all_of_shortNonneg

-- `XShortNonneg` for `n ≤ 8` (kernel check over `ℚ`)
#print axioms STUProof.xShortNonneg_le_8
#print axioms STUProof.stu_exists_le_8_of_unif
