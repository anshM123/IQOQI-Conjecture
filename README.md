# Symmetrically thermalizing unitaries exist (the IQOQI 2019 conjecture)

**Conjecture** (Bakhshinezhad, Clivaz, Vitagliano, Erker, Rezakhani, Huber, Friis, *J. Phys. A* **52**, 465303 (2019), arXiv:1904.07942; open in Clivaz's thesis, arXiv:2012.04321). Take:
- a local dimension d and a Hamiltonian H_A = H_B = H;
- a thermal state τ_β = e^{−βH}/Z;
- a target inverse temperature 0 ≤ β' ≤ β.

Then there is a global unitary U on C^d ⊗ C^d such that **both** marginals of U(τ_β ⊗ τ_β)U^† equal τ_{β'}.

Physically: correlations between two identical thermal systems can always be created at the minimal energy cost. Previously this was known only for d ≤ 4.

## What is proved, and how strongly

| # | statement | status | where |
|---|---|---|---|
| 1 | Conjecture for **every d ≤ 40**, no hypotheses | **machine-checked (Lean 4 + Mathlib)** | `lean/STUProof/KirwanFree40.lean`, theorem `STUProof.stu_exists_le_40` |
| 2 | Conjecture for **every d**, assuming Kirwan's convexity theorem (1984) in the symmetric form `KirwanSymmetricConvexity d` | machine-checked, conditional on that classical theorem | `lean/STUProof/STU.lean`, `STUProof.stu_exists` / `stu_exists_all` |
| 3 | Conjecture for **every d**, assuming ONE explicit elementary inequality `XShortNonneg n lo hi`: an explicit rational n×n matrix X(n,lo,hi) is ≥ 0 on its short diagonals | machine-checked reduction; inequality proved in Lean for n ≤ 8 | `lean/STUProof/KirwanFreeAllD.lean`, `STUProof.stu_exists_all_of_shortNonneg`; `ShortNonnegSmall.lean` |
| 4 | Conjecture for every d from **interval uniformisations** for all box sizes n ≤ d (`IntervalUnifAll n`) | machine-checked reduction | `lean/STUProof/KirwanFreeU.lean`, `STUProof.stu_exists_of_intervalUnif` |
| 5 | `IntervalUnifAll n` for **all n ≤ 140**, via an explicit construction with exact rational certificates (per-interval "dipole" construction). With #4 this gives the conjecture for **every d ≤ 140** | exact computer verification (Python `fractions`), two independent implementations | `certificates/per_interval_dipole/`, `code/coord_check_dip.py`, `logs/` |
| 6 | Conjecture for **every d** (paper proof, Kirwan route: explicit circulant construction + Kirwan convexity + Lemma 5) | proved on paper; numerically verified on 20 000 random instances (d ≤ 15); **external referee check requested** | `math/kirwan_route_all_d_REPORT.md` |
| 7 | Hook Decomposition Lemma HD(n) (a stronger combinatorial statement that also implies #4) for all n ≤ 102 | Doubling Lemma HD(M) ⇒ HD(2M) machine-checked; exact certificates for odd n ≤ 101 | `lean/STUProof/HookDoubling.lean`, `math/`, `logs/` |

The strong form "every spectrum majorised by the initial one is reachable" is **false** for d ≥ 4; an explicit counterexample is given in `math/kirwan_route_all_d_REPORT.md`.

**Open (in progress):** a proof of the inequality in #3, or of the per-interval construction in #5, for **all** n. That would make the Lean proof unconditional in every dimension. Both statements are verified exactly far beyond the needed small cases (#3 for n ≤ 76; #5 for n ≤ 140). See `PROOF_OVERVIEW.md` §5.

## Verify it yourself

### Lean (items 1–4, 7)
Requirements: [elan](https://github.com/leanprover/elan) (toolchain `leanprover/lean4:v4.33.1` is picked up from `lean/lean-toolchain`), about 7 GB RAM, about 20 minutes.
```bash
cd lean
lake exe cache get      # downloads the prebuilt Mathlib (pinned revision 0df444a3...)
bash check.sh           # elaborates every file in order, prints #print axioms, greps for sorry/admit/axiom/native_decide
```
Expected result:
- every main theorem prints `depends on axioms: [propext, Classical.choice, Quot.sound]`, which are Lean's three standard axioms;
- the keyword grep prints `none`.

Our full run is in `logs/lean_check_full_run.log` (exit 0 after 1076 s). The checks were run inside the `formal-conjectures` Lake environment with Mathlib at the same pinned revision; `lean/lakefile.toml` reproduces that dependency.

The statement being proved (from `KirwanFree40.lean`):
```lean
theorem stu_exists_le_40 {d : ℕ} (hd : d ≤ 40) (E : Fin d → ℝ) (hE : Monotone E) (β β' : ℝ)
    (hβ : 0 < β) (hβ'0 : 0 ≤ β') (hβ'β : β' ≤ β) :
    ∃ U ∈ unitaryGroup (Fin d × Fin d) ℂ,
      partialTraceB (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β' ∧
      partialTraceA (U * (gibbsState E β ⊗ₖ gibbsState E β) * star U) = gibbsState E β'
```
Here H = diag(E) with sorted energies. Sorting the energies and diagonalising a general H are local-unitary reductions.

### Exact certificates (items 5, 7)
Python ≥ 3.10, standard library only. Run from `code/`:
```bash
python coord_check_dip.py fast 2 140     # every interval [lo,hi] of every box n <= 140 (1-D exact criterion)
python coord_check_dip.py full 2 30      # full-matrix exact check (symmetry, [0,1], runs, rows)
python coord_check_hook.py               # hook decompositions n = 1..41 (odd n > 20 from ../certificates)
python coord_check_X.py 1 30             # the explicit cross construction X of item 3, all intervals, n <= 30
```

## Repository layout
- `PROOF_OVERVIEW.md`: the logical structure of the whole proof, with pointers.
- `lean/`: the Lean 4 project (`STUProof/*.lean`, `check.sh`, `lakefile.toml`, `lean-toolchain`).
- `math/`: the mathematical write-ups and working logs of every route.
- `certificates/`: exact hook decompositions (n ≤ 41) and per-interval dipole amplitudes (n ≤ 256; independently checked for n ≤ 140 so far).
- `code/`: independent exact checkers and the generators.
- `logs/`: our verification runs (Lean and Python).
- `research-log/`: the complete program log and the Lean formalisation log.

## References
- M. Bakhshinezhad, F. Clivaz, G. Vitagliano, P. Erker, A. T. Rezakhani, M. Huber, N. Friis, *Thermodynamically optimal creation of correlations*, J. Phys. A 52, 465303 (2019).
- F. Clivaz, PhD thesis, arXiv:2012.04321.
- F. Kirwan, *Convexity properties of the moment mapping III*, Invent. Math. 77, 547–552 (1984).
