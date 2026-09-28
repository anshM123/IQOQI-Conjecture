# Symmetrically thermalizing unitaries exist (the IQOQI 2019 conjecture)

**Conjecture** (Bakhshinezhad, Clivaz, Vitagliano, Erker, Rezakhani, Huber, Friis, *J. Phys. A* **52**, 465303 (2019), arXiv:1904.07942; open in Clivaz's thesis, arXiv:2012.04321). Take:
- a local dimension d and a Hamiltonian H_A = H_B = H;
- a thermal state τ_β = e^{−βH}/Z;
- a target inverse temperature 0 ≤ β' ≤ β.

Then there is a global unitary U on C^d ⊗ C^d such that **both** marginals of U(τ_β ⊗ τ_β)U^† equal τ_{β'}.

Physically: correlations between two identical thermal systems can always be created at the minimal energy cost. Previously this was known only for d ≤ 4.

> **Status (2026-09-28):** the conjecture is proved for **every dimension d without Kirwan's theorem**:
> - an elementary, explicit proof whose reduction step is **machine-checked in Lean** (row 4 below);
> - the remaining lemma is proved **for all n** on paper, with six one-parameter facts verified exactly by two independent computer methods (row 8);
> - it is machine-checked in Lean with **no hypotheses at all for d ≤ 40**.
>
> The Lean formalisation of the last lemma, which would make the all-d Lean proof hypothesis-free, is in progress.

## What is proved, and how strongly

| # | statement | status | where |
|---|---|---|---|
| 1 | Conjecture for **every d ≤ 40**, no hypotheses | **machine-checked (Lean 4 + Mathlib)** | `lean/STUProof/KirwanFree40.lean`, theorem `STUProof.stu_exists_le_40` |
| 2 | Conjecture for **every d**, assuming Kirwan's convexity theorem (1984) in the symmetric form `KirwanSymmetricConvexity d` | machine-checked, conditional on that classical theorem | `lean/STUProof/STU.lean`, `STUProof.stu_exists` / `stu_exists_all` |
| 3 | Conjecture for **every d**, assuming ONE explicit elementary inequality `XShortNonneg n lo hi`: an explicit rational n×n matrix X(n,lo,hi) is ≥ 0 on its short diagonals | machine-checked reduction; inequality proved in Lean for n ≤ 8 | `lean/STUProof/KirwanFreeAllD.lean`, `STUProof.stu_exists_all_of_shortNonneg`; `ShortNonnegSmall.lean` |
| 4 | Conjecture for every d from **interval uniformisations** for all box sizes n ≤ d (`IntervalUnifAll n`) | machine-checked reduction | `lean/STUProof/KirwanFreeU.lean`, `STUProof.stu_exists_of_intervalUnif` |
| 5 | `IntervalUnifAll n` for **all n ≤ 256**, via an explicit construction with exact rational certificates (per-interval "dipole" construction). With #4 this gives the conjecture for **every d ≤ 256** (now subsumed by #8) | exact computer verification (Python `fractions`), two independent implementations | `certificates/per_interval_dipole/`, `code/coord_check_dip.py`, `logs/` |
| 6 | Conjecture for **every d** (paper proof, Kirwan route: explicit circulant construction + Kirwan convexity + Lemma 5) | proved on paper; numerically verified on 20 000 random instances (d ≤ 15); **external referee check requested** | `math/kirwan_route_all_d_REPORT.md` |
| 7 | Hook Decomposition Lemma HD(n) (a stronger combinatorial statement that also implies #4) for all n ≤ 102 | Doubling Lemma HD(M) ⇒ HD(2M) machine-checked; exact certificates for odd n ≤ 101 | `lean/STUProof/HookDoubling.lean`, `math/`, `logs/` |
| 8 | **`IntervalUnifAll n` for EVERY n**, via an explicit one-dipole construction. Together with #4 this gives the **conjecture for every d, without Kirwan** | **complete paper proof**. The only computer inputs are six one-parameter facts F1–F6 (about a(K) = 4K²(−1)^K(ln 2 − Σ_{i≤K}(−1)^{i−1}/i) + 1 − 2K), verified exactly by two independent methods; the construction is also exact-checked for all intervals n ≤ 170 and sampled up to n = 4000 | `math/UNIF_all_n_PROOF.md`, `code/verify_facts.py`, `code/coord_facts.py`, `logs/unif_all_n_*` |

The strong form "every spectrum majorised by the initial one is reachable" is **false** for d ≥ 4; an explicit counterexample is given in `math/kirwan_route_all_d_REPORT.md`.

**Remaining (in progress):** the Lean formalisation of #8, a finite algebraic argument plus elementary analysis of β(x) = Σ_{j≥0}(−1)^j/(x+j) (see `math/UNIF_all_n_PROOF.md`, §8 'Lean notes'). This will make the all-d Lean proof hypothesis-free. Item #3 (the cross construction X) is superseded by #8 and is kept as an alternative route.

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
python coord_check_dip.py fast 2 256     # every interval [lo,hi] of every box n <= 256 (1-D exact criterion)
python coord_check_dip.py full 2 30      # full-matrix exact check (symmetry, [0,1], runs, rows)
python coord_check_hook.py               # hook decompositions n = 1..41 (odd n > 20 from ../certificates)
python coord_check_X.py 1 30             # the explicit cross construction X of item 3, all intervals, n <= 30
python verify_facts.py                   # facts F1-F6 of the all-n proof (item 8), exact
python coord_facts.py                    # the same facts, independent method (interval arithmetic + Sturm)
```

## Repository layout
- `PROOF_OVERVIEW.md`: the logical structure of the whole proof, with pointers.
- `lean/`: the Lean 4 project (`STUProof/*.lean`, `check.sh`, `lakefile.toml`, `lean-toolchain`).
- `math/`: the mathematical write-ups and working logs of every route.
- `certificates/`: exact hook decompositions (n ≤ 41) and per-interval dipole amplitudes (n ≤ 256; all independently checked).
- `code/`: independent exact checkers and the generators.
- `logs/`: our verification runs (Lean and Python).
- `research-log/`: the complete program log and the Lean formalisation log.

## References
- M. Bakhshinezhad, F. Clivaz, G. Vitagliano, P. Erker, A. T. Rezakhani, M. Huber, N. Friis, *Thermodynamically optimal creation of correlations*, J. Phys. A 52, 465303 (2019).
- F. Clivaz, PhD thesis, arXiv:2012.04321.
- F. Kirwan, *Convexity properties of the moment mapping III*, Invent. Math. 77, 547–552 (1984).
