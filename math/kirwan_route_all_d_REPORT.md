# P-STU — Symmetrically thermalizing unitaries exist in every local dimension

Status: PROOF (work package P-STU), independently re-verified (logic traced by hand; own code
`verify_alld_coord.py`: 20000 random instances d ≤ 15, all k, marginal error ≤ 3.3e-16, min β_r = 0.0139 > 0; Lemma 5 LP 0/3000 failures).
Needs an external expert check before circulation. The only non-elementary input is Kirwan's convexity theorem.

## Statement
Conjecture (Bakhshinezhad, Clivaz, Vitagliano, Erker, Rezakhani, Huber, Friis, J. Phys. A 52, 465303 (2019), arXiv:1904.07942; still open in
Clivaz, arXiv:2012.04321): for every H_A = H_B on C^d, every β > 0 and β′ ∈ [0, β], there is a unitary U on C^d⊗C^d such that both marginals of
U(τ_β⊗τ_β)U† equal τ_{β′}. Previously proved for d ≤ 4 (and equally spaced spectra).

## Proof
Notation: p = spec τ_β sorted decreasingly; n = k+1; T = {0..n−1}; tails J = {n..d−1}; π = p|_T; P = Σπ; Q = 1−P; a = P/n;
v_k = (a,…,a, p_n,…,p_{d−1}). S(λ) = {q : (q,q) is a pair of sorted marginal spectra of some ρ in the unitary orbit of diag(λ)}.

Step 1 (explicit, all d, k, p): v_k ∈ S(p⊗p). Start from diag(p⊗p) in the product basis |i j⟩.
 (a) Tail relabelling: for each tail j pick r_j = (j−n) mod n and permute |i j⟩ → |i+r_j, j⟩, |j i⟩ → |j, i+r_j⟩ (i ∈ T, indices mod n).
     Permutation ⇒ state stays diagonal; row/column i ∈ T receives p_j π_{i−r_j}; rows/columns j keep total p_j(P+Q) = p_j.
     W_r := Σ_{j: r_j = r} p_j.
 (b) Circulant mixing in T×T: β_r = (1/n − W_r)/P, B = Σ_r β_r Π^r ((Π^r v)_i = v_{i−r}). Σ_r β_r = (1−Q)/P = 1.
     Each cyclic diagonal D_s = {|i, i+s⟩ : i ∈ T} has distinct rows and distinct columns. On span(D_s) apply a unitary (Schur–Horn; exact
     Chan–Li rotations in code) taking diag(λ^{(s)}), λ^{(s)}_i = π_iπ_{i+s}, to a state whose diagonal is Bλ^{(s)} (possible since Bλ ≺ λ).
     Coherences inside D_s do not enter the marginals (distinct rows/columns), so both marginals stay diagonal.
 (c) Marginals: row i ∈ T: Σ_s (Bλ^{(s)})_i + Σ_r W_r π_{i−r} = Σ_r (Pβ_r + W_r) π_{i−r} = (1/n) Σ_r π_{i−r} = a. Columns identical by symmetry
     of the computation. Tail rows/columns: p_j. Hence both marginals are diag(v_k).
 (d) β_r ≥ 0: with tails q_0 ≥ q_1 ≥ … (q_t = p_{n+t}), W_r = q_r + Σ_{ℓ≥1} q_{r+ℓn} and q_{r+ℓn} ≤ average of the n preceding tails, so
     W_r ≤ q_r(1−1/n) + Q/n ≤ P/n + Q/n = 1/n, because q_r ≤ p_n ≤ min π ≤ P/n.  (J = ∅: B = uniform = Bell averaging; n = 1 trivial.)
Step 2 (convexity): Kirwan (Invent. Math. 77, 547 (1984)) for the orbit of diag(p⊗p) under U(d)×U(d) with moment map ρ ↦ (Tr_Bρ, Tr_Aρ):
 the set of sorted marginal-spectrum pairs is a convex polytope (as in Klyachko quant-ph/0409113; Christandl–Mitchison CMP 2006).
 Its symmetric slice S(p⊗p) is convex, hence ⊇ conv{v_0,…,v_{d−1}}.
Step 3 (Lemma 5 of 1904.07942, App. A.X; re-proved): spec τ_{β′} ∈ conv{v_0,…,v_{d−1}} for β′ ∈ [0, β]. Re-proof: with w = e^{−βE},
 N_m = Σ_{i≤m}(w_i − w_{m+1}), membership ⇔ N_m/N_{m+1} non-decreasing in β and 1 − d·p_{d−1} increasing; log-derivative argument with x e^x ≥ e^x − 1.
Step 4: local unitaries rotate both marginals to τ_{β′}. ∎

## Additional results
- The strong form "every q ≺ p is a reachable symmetric marginal of p⊗p" is FALSE for all d ≥ 4.
  **Corrected 2026-09-28.** The family originally written here (δ = 0.05 fixed, ε = 2δ², more ε's for larger d) proves this only for 4 ≤ d ≤ 8.
  The key inequality fails for d ≥ 9. The following family works for EVERY d ≥ 4:
  δ = 1/(5d), η = 2δ², p = (1−δ−(d−2)η, δ, η, …, η), s = 1−p_0, q = (p_0, s/(d−1), …, s/(d−1)) ≺ p.
  For d = 4 it is p = (0.94, 0.05, 0.005, 0.005), q = (0.94, 0.02, 0.02, 0.02).
  Proof:
  1. After a local unitary, |0⟩ is the p_0-eigenvector of both marginals.
  2. Ky Fan: Tr[(|0⟩⟨0|⊗1 + 1⊗|0⟩⟨0|)ρ] = 2p_0 = λ_1 + (λ_1+…+λ_{2d−1}). The gaps λ_1 > λ_2 and λ_{2d−1} > λ_{2d} force ρ = λ_1|00⟩⟨00| ⊕ ρ_O ⊕ ρ_R, with O = span{|0j⟩,|j0⟩} and Tr ρ_R = s².
  3. The block of ρ_A on span{|j⟩: j ≥ 1} is Y + Z, with Y a compression of ρ_O and Z = Tr_B ρ_R. Weyl and Cauchy interlacing give
     λ_3(Y+Z) ≤ p_0η + s² < 4δ² = 4δ/(5d) < s/(d−1).
     This contradicts the flat target.
  Full proof: the manuscript (Prop. "strong majorization form is false"). Exact check of the inequalities for 4 ≤ d ≤ 400.
- S(p⊗p) can leave the majorisation polytope (d = 3 example p = (.4,.35,.25) reaches (.4075,.335,.2575)).
- Earlier construction (C) with exact rational certificates for d = 5, 6, 7 (certs.py) remains independent confirmation.

## Files
alld_construction.py (explicit unitaries), verify_alld_coord.py (independent check), lc.py, v2_construction.py, certs.py, certify_c.py,
cond_c.py, check_lemma5.py, LOG.md.
