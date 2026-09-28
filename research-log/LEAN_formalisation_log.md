# P-LEAN-STU log: symmetrically thermalizing unitaries (STUs) in every local dimension

Goal: machine-check (Lean 4 + Mathlib, no `sorry`, no new axioms) the proof in
`iqoqi/programs/stu/REPORT.md` of the conjecture of Bakhshinezhad, Clivaz, Vitagliano, Erker,
Rezakhani, Huber, Friis, J. Phys. A 52, 465303 (2019), arXiv:1904.07942.

Toolchain: `leanprover/lean4:v4.33.1`, Mathlib from the existing `.lake` cache (no rebuild, no
`lake update`). `import Mathlib` peak RAM ~3.2 GB.

## How to check

From the project root `formal-conjectures/`, with `C:\Users\anshm\.elan\bin` on `PATH`:

    bash STUProof/check.sh

The script elaborates `SchurHorn`, `Construction`, `Lemma5`, `STU`, `KirwanFreeCore`,
`KirwanFreeHook`, `HookCertificates`, `KirwanFree`, `HookDoubling`, `HookCertSplit`,
`HookCert21`, `HookCert23`, …, `HookCert39`, `KirwanFree40`, `IntervalUnif`, `KirwanFreeU`,
`Renewal`, `CrossUnif`, `KirwanFreeAllD`, `ShortNonnegSmall` (each `STUProof/<F>.lean`) in this
order with `lake env lean` (writing each `.olean` to the git-ignored
`.lake/build/lib/lean/STUProof/` so the next file can `import` it), then runs `Axioms.lean`
(`#print axioms`) and greps for `sorry/admit/axiom/native_decide`. Total and peak RAM: see the
P-LEAN-UNIF section (before P-LEAN-DBL: ~5 min, 4.8 GB). No repository file outside `STUProof/` is
modified.

## Status

Two independent routes, both fully checked:

1. **Kirwan-free route (P-STU3)**: `stu_exists_kirwanFree (hH : ∀ n ≤ d, HookDecomposition n)`,
   the only hypothesis being the spectrum-independent Hook Decomposition Lemma; **unconditional
   for `d ≤ 40`** (`stu_exists_le_40`: kernel-checked certificates for `n ≤ 20` and odd
   `n ≤ 39`, doubling lemma `hookDecomposition_double` for even `n`; earlier `stu_exists_le_20`).
   The Hook Decomposition Lemma is proved for every `n` whose odd part is at most `39`
   (`hookDecomposition_two_pow_mul_le_40`). See the sections below.
   **All dimensions (P-LEAN-UNIF)**: `stu_exists_all_of_shortNonneg` reduces the conjecture in
   every dimension to the single explicit inequality `XShortNonneg n lo hi` (nonnegativity of the
   explicit cross construction on its short runs, `1 ≤ lo ≤ hi ≤ n-2`), proved for `n ≤ 8`.
2. **Kirwan route (P-STU)**: `stu_exists (hK : KirwanSymmetricConvexity d)`.

### Kirwan route: COMPLETE modulo the single explicit hypothesis `KirwanSymmetricConvexity d`

| file | content | status |
|---|---|---|
| `SchurHorn.lean` | real Schur–Horn existence theorem `schurHorn` | proved |
| `Construction.lean` | Step 1: `exists_constr`, `vk_reachable` | proved, unconditional |
| `Lemma5.lean` | Step 2: `conv_vN`, `lemma5`, `gibbs_mem_convexHull` | proved |
| `STU.lean` | Steps 3–4, `stu_exists`, `stu_exists_all` | proved from `hK` |

`#print axioms` of `schurHorn`, `exists_constr`, `vk_reachable`, `lemma5`,
`gibbs_mem_convexHull`, `vk_mem_symMarginalSpectra`, `symMarginalSpectra_eq`,
`symMarginalSpectra_eq_charpoly`, `stu_of_mem_symMarginalSpectra`, `stu_exists`, `stu_exists_all`:
`[propext, Classical.choice, Quot.sound]` only. Schur–Horn is NOT a hypothesis.

## Progress

- 2026-09-28 01:10 Read REPORT.md, alld_construction.py, check_lemma5.py, LOG.md of P-STU and
  TMProof/TM.lean. Design decisions:
  * Majorization in the sorting-free "hockey-stick" form: `x ≺ y` iff equal sums and
    `∑ (x_i - t)⁺ ≤ ∑ (y_i - t)⁺` for all `t` (`MajOn`). Then `Bλ ≺ λ` for doubly stochastic
    circulant `B` is Jensen, and Schur–Horn can be proved by induction without sorting.
  * Construction on the index type `(Fin n ⊕ J) × (Fin n ⊕ J)` (top block `T = Fin n`, `n = k+1`,
    with cyclic arithmetic of `Fin n`; tails `J`), split into four sectors by an explicit
    equivalence; the orthogonal matrix is `fromBlocks` of block-diagonal pieces; the final result
    is transported to `Fin d` by `finSumFinEquiv`.
  * Tail shifts from a greedy bin-packing argument (no sorting of tails needed): put each tail
    into the currently lightest bin; needs only `q_j ≤ min π`. (Replaces the round-robin shifts
    of the paper proof; same bound `W_r ≤ 1/n`.)
- 01:23 `SchurHorn.lean` COMPLETE: `schurHorn` via Chan–Li-type induction. Invariant: `M` is
  diagonal on the set `U` of unfinished indices. Pick `i₀ = argmax x`, `j₁ = argmax diag`,
  `j₂ = argmax{diag_j : j ≠ j₁, diag_j ≤ x_{i₀}}`; Givens rotation in the plane `(j₁, j₂)` puts
  `x_{i₀}` at `j₁` and `m₁ + m₂ - x_{i₀}` at `j₂`; a transposition moves the finished entry to
  `i₀`. Combinatorial core `maj_step` (three cases in `t`; the middle range `m₂ < t < x_{i₀}`
  uses a counting argument).
- 01:34 `Construction.lean` COMPLETE: `exists_constr` (Step 1 on `(Fin n ⊕ J)²`),
  `vk_reachable` (Step 1 on `Fin d`). The nonnegativity of the top weights `π` turned out not to
  be needed. Schur–Horn is applied on each cyclic diagonal with `B = ∑ β_c Π^c`
  (`majOn_circulant`); marginals computed sector by sector (`partialTraceB_sectorState`,
  `partialTraceA_sectorState`, `row_T`, `col_T`).
- 01:43 `Lemma5.lean` COMPLETE: explicit barycentric coordinates `c_k = ρ_k - ρ_{k-1}`
  (`ρ_{-1} = 0`, `ρ_{d-1} = 1`), `ρ_m = F_m(q)/F_m(p)`, `F_m(u) = u_0+…+u_m - (m+1)u_{m+1}`
  (`conv_vN`, abstract; `lemma5`, Gibbs). `F_m(v_k) = [k ≤ m] F_m(p)` (`fF_vN`) and injectivity
  of `u ↦ (∑u, F_0(u), …)` (`eq_zero_of_fF`) give `q = ∑ c_k v_k`. Monotonicity of `ρ` is,
  term by term, the three-point inequality `three_point`
  `(e^{-β'a}-e^{-β'b})(e^{-βb}-e^{-βc}) ≤ (e^{-β'b}-e^{-β'c})(e^{-βa}-e^{-βb})` (`a ≤ b ≤ c`),
  proved from `exp_chord`: `β(e^{β'y}-1) ≤ β'(e^{βy}-1)` (convexity of `exp`). `ρ_{d-2} ≤ 1` is
  `p_{d-1} ≤ q_{d-1}` (`gibbs_top_le`). Degenerate levels (`F_m(p) = 0`) use `x/0 = 0` and
  `F_m(p) = 0 → F_m(q) = 0` (equal energies).
- 02:04 `STU.lean` COMPLETE: `stu_exists (hK : KirwanSymmetricConvexity d)`, Step 4 via
  `partialTraceB_conj_kronecker` / `partialTraceA_conj_kronecker` (local unitaries `V ⊗ W`),
  complexification of real orthogonal matrices, and two restatements of the hypothesis' set:
  `symMarginalSpectra_eq` (Weyl-chamber form: marginals exactly `diag q`) and
  `symMarginalSpectra_eq_charpoly` (characteristic polynomials `∏ (X - q_i)`, via the spectral
  theorem `exists_unitary_conj_iff_charpoly`). Modular reduction
  `stu_of_mem_symMarginalSpectra` (unconditional): a Kirwan-free proof only needs to show
  `gibbs E β' ∈ symMarginalSpectra (gibbs E β ⊗ gibbs E β)`.
- 02:06 Final `bash STUProof/check.sh`: all files check, no warnings, axioms as above, grep finds
  no `sorry/admit/axiom/native_decide`.

## Remaining / possible extensions

- The only unproved input is `KirwanSymmetricConvexity d` (Kirwan 1984). It is used only in
  `gibbs_mem_symMarginalSpectra`, and only for `w = p ⊗ p`.
- Statement uses `H = diag(E)` with `E` sorted increasingly (WLOG in physics). Not formalized:
  the reduction from an arbitrary Hermitian `H` (spectral theorem + `Matrix.exp_conj`) and from
  unsorted `E` (permutation); both are local-unitary conjugations handled by the Step-4 lemmas.

## Kirwan-free route (P-STU3), 2026-09-28 03:10–06:50 (final check 06:44: all files, 25 axiom checks, peak 4.6 GB)

Files (new; the Kirwan-route files are unchanged):

| file | content |
|---|---|
| `KirwanFreeCore.lean` | `lc_reachable` (LC blocks + Schur–Horn → orthogonal `O`), `SMaj` (subset-form majorization: superposition `SMaj.add/sum/smul`, `SMaj.majOn`, `smaj_self`, `smaj_zeroOne`), tri-run structure `tri_reachable`, `ReachTri` + `ReachTri.convex` (fixed-structure convexity), Lemma T (`lemmaT`, `thermal_clip_weights`) |
| `KirwanFreeHook.lean` | `IsHookDecomposition`/`HookDecomposition` (run form, exactly the `exact_hookdec.py` header), symmetric cell form `hookCell` (runs, rows, cells), uniformisation `unif` of hook intervals, crosses `crossInd`, `unif_smaj`, cell counts `crossInd_sum` |
| `KirwanFree.lean` | `w_k` construction: `wk_cell_identity` (p⊗p = B⊗B + Σ ω(Q + U)), `wk_mass`, Hall slack `leftM_nonneg`, `Ltot_pos`, `wk_smaj`, `wk_rows`, `wk_reach`; `gibbs_reachTri`; `stu_exists_kirwanFree`, `stu_exists_of_hookDecomposition`, `stu_exists_le_20` |
| `HookCertificates.lean` | exact hook decompositions `n = 1..20` (data of `stu3/hookdec_n{n}.txt`, scaled by a common denominator to naturals), each checked by `decide +kernel`; `hookDecomposition_of_nat`; `hookDecomposition_le_20` |

Notes:
- Lemma T is proved for any concave, monotone `g` with `g 0 ≥ 0` (chord-slope sequence
  `slopeSeq`, ties handled by repeating the previous slope), then used with `g = x^{β'/β}`
  (`gibbs_rpow`: `Gibbs(β') ∝ Gibbs(β)^{β'/β}`).
- Superposition is formalized with subset-form majorization `∑_S x ≤ λ_0+…+λ_{|S|-1}`, which is
  linear; `SMaj.majOn` converts to the hockey-stick form used by `schurHorn`.
- Hall slack: `leftM_M ≥ (M+1) c_M (1-Z)²/Z ≥ 0` (the `E²/Z` part of `E²(M+1)/Z + F`, using
  `hmass(M-m, M) ≤ 2(m+1)(M+1)` and `∑_{m<k}(m+1)c_m = 1 - Z`); `Ltot > 0` whenever some
  `c_m ≠ 0`, `m < k` (else all weights vanish).
- Flexible pieces are spread over the boxes `[0, M']`, `M' ≥ k`, with weights `left_{M'}/L`;
  `flex_mass` shows that their total mass is `L` (via the cell identity and cell counts).
- Certificates: `decide +kernel` (kernel reduction only; no `native_decide`, no extra axioms);
  common denominators up to 36 digits (n = 20). All 20 in one file: ~60 s, 4.4 GB.
- `#print axioms` for `stu_exists_kirwanFree`, `stu_exists_of_hookDecomposition`,
  `hookDecomposition_le_20`, `stu_exists_le_20` (and all lemmas above):
  `[propext, Classical.choice, Quot.sound]`.
- Plug-in point for an all-`n` proof: `stu_exists_of_hookDecomposition (hH : ∀ n, HookDecomposition n)`.

## Doubling lemma and `d ≤ 40` (P-LEAN-DBL), 2026-09-28 07:40–08:45

Final check 08:27–08:43: `bash STUProof/check.sh` exit code 0 (all 22 files, no warnings),
952 s wall (~16 min; the certificate files ~10 min of it), peak RAM 4.64 GB (one Lean process at a
time), 33 `#print axioms` checks, all `[propext, Classical.choice, Quot.sound]`; the grep for
`sorry/admit/axiom/native_decide` finds none.

Math: P-HOOK doubling lemma (`iqoqi/programs/hook/LOG.md`). From a hook decomposition `(Y_c)_{c<M}`
of the `M`-box, the `2M`-box (`A = [0, M)`, `B = [M, 2M)`) gets the hooks `c < M`: `Y_c / 2` on
`A × A` and `B × B`; and `M + c`: `Y_{M-1-c} / 2` on `A × A` and `B × B` plus `Y_c` on the cross
blocks (`(i, M + j)` and `(M + j, i)` get `Y_c(i, j)`).

Files (new; no existing statement changed):

| file | content |
|---|---|
| `HookDoubling.lean` | cell form `IsHookCells n W` (symmetric, zero off the box, nonnegative, runs `∑_i W a i (i+s) = [s ≤ a]`, rows `(2a+1)/n`, cells `∑_{a<n} W a i j = 1`); `isHookCells_hookCell` (via `hookCell`), `IsHookCells.isHookDecomposition` (`x a s i := W a i (i+s)`), `hookDecomposition_iff_cells`; derived `band`, `run_lower`, `run_cross`; block form `dblCell M D C` (`D/2` on `A×A`, `B×B`, `C` on `A×B` and mirrored), doubled family `dblW`; `IsHookCells.double`; `hookDecomposition_double`, `hookDecomposition_two_pow_mul`, `hookDecomposition_pow2` |
| `HookCertSplit.lean` | the pieces `HookRunNat`, `HookRowNat` (runs and rows of one hook `a`) and `HookCellNat` (cells of one run `s`) of `IsHookDecompositionNat`; `isHookDecompositionNat_of_split`, `forall_lt_succ_of` |
| `HookCert{n}.lean`, `n = 21, 23, …, 39` | exact certificates `iqoqi/programs/hook/certs/hookdec_n{n}.txt` (re-checked with `stu3/coord_check_hook.py` before generation), common denominator `D` (42 to 185 digits), generated by `iqoqi/programs/hook/gen_lean_certs.py`; `3n` pieces `hookNat{n}_run_a`, `_row_a`, `_cell_s`, each by `decide +kernel`; `hookNat{n}_valid`, `hookDecomposition_{n}` |
| `KirwanFree40.lean` | `hookDecomposition_le_40`, `hookDecomposition_two_pow_mul_le_40`, `stu_exists_le_40` |

Main statements:
- `hookDecomposition_double {M : ℕ} (h : HookDecomposition M) : HookDecomposition (2 * M)`
- `hookDecomposition_two_pow_mul {m : ℕ} (h : HookDecomposition m) : ∀ k, HookDecomposition (2 ^ k * m)`
- `hookDecomposition_pow2 : ∀ k, HookDecomposition (2 ^ k)`
- `hookDecomposition_le_40 : ∀ n ≤ 40, HookDecomposition n`
- `hookDecomposition_two_pow_mul_le_40 (k : ℕ) {m : ℕ} (hm : m ≤ 40) : HookDecomposition (2 ^ k * m)`
  (every box size whose odd part is at most `39`)
- `stu_exists_le_40`: the statement of `stu_exists_le_20` with `hd : d ≤ 40`.

Notes:
- Doubling proof, in cell form. Runs: `dblCell_run` gives `∑_{i<M} D i (i+s)` (both diagonal
  blocks) plus the cross part `∑_{i<M} [M ≤ i+s] C i (i+s-M)`. `run_cross` evaluates the cross
  part as `[M - c ≤ s ≤ M + c]`, using the upper runs of `Y_c` for `s ≥ M` and the lower runs
  (`run_lower`, by symmetry) for `s < M`. Then `[s ≤ M-1-c] + [M-c ≤ s ≤ M+c] = [s ≤ M+c]`.
  Rows: `dblCell_row_A/B`. Cells: `Finset.sum_range_reflect` for `∑_c Y_{M-1-c}`.
- Certificates, kernel memory. A single `decide +kernel` over all constraints of `n = 39` went
  over 7.5 GB and was stopped. The split pieces were also stopped at 7.5 GB under the default
  parallel elaboration (`Elab.async`, on for the command line), which runs many kernel checks at
  once. With `set_option Elab.async false` (in each `HookCert{n}.lean`) the pieces are checked one
  after the other. All 39 row pieces of `n = 39` take 28 s of kernel time at a peak of 3.5 GB.
  Compile times of the certificate files: `n = 21`: 31 s, …, `n = 37`: 91 s, `n = 39`: 115 s.
- Data definition `hookNat39`: the first attempt stopped with `maximum recursion depth` at the
  `def`. The generator now sets `maxRecDepth` and writes lists with at least 32 entries as `::`
  chains; the `[...]` macro expands such long literals via untyped `let`s
  (`Init/NotationExtra.lean`, `%[...]`). The `n = 39` data then elaborate in 4.4 s. Which of the
  two changes is necessary was not isolated.
- No `native_decide`; `#print axioms` of all new main theorems (and of `hookDecomposition_39`):
  `[propext, Classical.choice, Quot.sound]`.


## Interval uniformisations: all dimensions from one inequality (P-LEAN-UNIF), 2026-09-28 09:05–12:10

Math: P-UNIF (`iqoqi/programs/unif/LOG.md`). `KirwanFree.lean` uses a hook decomposition only
through `unif (M+1) (X (M+1)) lo hi`, and only through: symmetric, entries in `[0, 1]`, zero off the
box, run `s` total `#{a ∈ [lo, hi] : s ≤ a}`, row totals `hmass lo hi / n`, each interval
independently. These properties are `IsIntervalUnif n lo hi u`.

Final check 11:47–12:05: `bash STUProof/check.sh` exit code 0 (all 28 files, no errors or
warnings), 1089 s wall (~18 min), peak RAM 6.36 GB (`ShortNonnegSmall.lean`; everything else
≤ 4.6 GB), one Lean process at a time. All 44 `#print axioms` lines are
`[propext, Classical.choice, Quot.sound]`; the grep for `sorry/admit/axiom/native_decide` finds
none.

Files (new; no existing statement changed):

| file | content |
|---|---|
| `IntervalUnif.lean` | `IsIntervalUnif`, `IntervalUnifAll n` (all `lo ≤ hi < n`); `run'`, `row'` (any range), `IsIntervalUnif.smaj` (run majorization by the crosses); `isIntervalUnif_unif`, `intervalUnifAll_of_hookDecomposition`; `card_filter_Icc_le`, `sum_Icc_odd` |
| `KirwanFreeU.lean` | the `w_k` construction with a family `U n lo hi` in place of `unif` (`flexUU`, `compGU`, `wkConfigU`, `wkU_smaj`, `wkU_rows`, `wkU_reach`; all `X`-free lemmas of `KirwanFree.lean` reused), `exists_unifData`, `gibbs_reachTri_of_intervalUnif`, `stu_exists_of_intervalUnif` |
| `Renewal.lean` | renewal square `renU n m` (`m ≤ n-2`) in Toeplitz+Hankel form `A(|i-j|+1) + A(min(i+j+2, 2n-i-j))`, `A(p) = ∑_t (-1)^t H(p+t)`; `isIntervalUnif_renU` (`[0, m]`), `isIntervalUnif_boxJ` (`J`, `[0, n-1]`), `IsIntervalUnif.compl` (`J - U`, `[m+1, n-1]`) |
| `CrossUnif.lean` | windows `place`, `avgPlace`, `covW`; `crossTheta`, `crossX` (the cross construction); `XShortNonneg`; `isIntervalUnif_crossX` |
| `KirwanFreeAllD.lean` | `intervalUnifAll_of_shortNonneg`, `stu_exists_of_shortNonneg`, `stu_exists_all_of_shortNonneg` |
| `ShortNonnegSmall.lean` | mirror `crossXQ` over `ℚ`, `crossXQ_cast`, kernel check `shortOKQ_le_8`; `xShortNonneg_le_8`, `stu_exists_le_8_of_unif` |

Main statements:
- `stu_exists_of_intervalUnif {d} (hU : ∀ n ≤ d, IntervalUnifAll n)`: the STU statement for `d`.
- `XShortNonneg n lo hi := ∀ i j, i < n → j < n → Nat.dist i j < lo → 0 ≤ crossX n lo hi i j`, with
  `crossX = θ U^hi_n + (1-θ) avg_t J[W_t] - ½ U^{lo-1}_n - ½ avg_t U^{lo-1}_b[W_t]`, `b = hi+1`,
  `W_t = [t, t+hi]`, `t = 0, …, n-b`, `θ = 1 - lo²/(2b²)`. This is the only open input.
- `stu_exists_of_shortNonneg {d} (h : ∀ n ≤ d, ∀ lo hi, 1 ≤ lo → lo ≤ hi → hi + 2 ≤ n →
  XShortNonneg n lo hi)`: the STU statement for `d`.
- `stu_exists_all_of_shortNonneg (h : ∀ n lo hi, 1 ≤ lo → lo ≤ hi → hi + 2 ≤ n →
  XShortNonneg n lo hi)`: the STU statement for all `d`.
- `xShortNonneg_le_8`: `XShortNonneg n lo hi` for all `n ≤ 8`; hence `stu_exists_le_8_of_unif`
  (a second proof for `d ≤ 8`, with no hook decompositions).

Notes:
- Renewal square. The block construction (reversal permutations of the blocks `[0,ℓ-1]`,
  `[n-ℓ,n-1]` with weight `H(ℓ)` and `[a,a+ℓ-1]` with weight `H(ℓ)-H(ℓ+1)`) has the cell form
  `U(i,j) = A(|i-j|+1) + A(min(i+j+2, 2n-i-j))`. I checked this exactly against the coordinator's
  block implementation (`unif/coord/coord_check_X.py`, `renewal`): all `n ≤ 30`, `m ≤ n-2`, 206,770
  cells. Lean works with this form only.
  * `A(p) + A(p+1) = H(p)` (`renA_add`). `U(i,j) = A(p) + A(p+2k+1)`, `p = |i-j|+1`,
    `k = min(i, j, n-1-i, n-1-j)` (`renU_eq`). This is `∑_{t ≤ 2k} (-1)^t H(p+t)`, which lies in
    `[0, H(p)]` because `H` is nonincreasing and nonnegative (`renB_bounds`, by pairing terms).
  * Band: `U = 0` for `|i-j| > m`.
  * Rows: moving from row `r` to row `r+1` adds `A(r+2) - A(n-r)` to the Toeplitz part and removes
    the same amount from the Hankel part (`renU_row_succ`). Row 0 is `∑_ℓ H(ℓ) = (m+1)²/n`, by
    telescoping `K²/((x)(x+1)) = K²(1/x - 1/(x+1))`.
  * Runs: `R(s) = W(s+1) + R(s+2)` (`renR_rec`), with `W(ℓ) = 2H(ℓ) + (n-ℓ-1)(H(ℓ)-H(ℓ+1))`,
    `W = 2` for `ℓ ≤ m` and `W(m+1) = 1`. Downward induction gives `R(s) = m+1-s`.
- Cross construction. Placed and averaged windows keep run totals (`avgPlace_run`). Their row
  totals are `covW · (row of V)/(n+1-b)` (`avgPlace_row`); the `covW` terms cancel because
  `(1-θ) b = lo²/(2b)`.
  * `X ≤ 1`, since `θ, 1-θ ≥ 0` and the subtracted terms are nonnegative.
  * `X ≥ 0` on runs `≥ lo`, since both `U^{lo-1}` terms vanish there by the band property.
- Faithfulness of `XShortNonneg`. A Python transcription of the Lean definitions (`renU`, `place`,
  `avgPlace`, `crossTheta`, `crossX`, with ℕ truncated subtraction) equals the coordinator's
  independent `X_matrix` exactly in all 560 cases `1 ≤ lo ≤ hi ≤ n-2`, `n ≤ 16`. Its short-run
  entries are all `≥ 0`, so the stated hypothesis is the intended inequality, and it holds there.
- Small `n`. `ℝ` is not computable, so `crossX` is mirrored over `ℚ` with the same formulas and cast
  back (`crossXQ_cast`, by `push_cast`). The single statement `∀ n < 9, …` failed instance
  synthesis for `Decidable`; the inner cell condition is therefore a `def ShortOKQ` with an
  `inferInstanceAs` instance. `decide +kernel` then takes 36 s of kernel time at a peak of 6.4 GB.
- No `native_decide`, no `sorry`; `#print axioms` of all new main theorems:
  `[propext, Classical.choice, Quot.sound]`.
