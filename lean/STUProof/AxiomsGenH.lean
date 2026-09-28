import STUProof.GeneralH

/-! Axiom check for the general-Hamiltonian results (run after building `GeneralH`, see
`check_genh.sh`). -/

-- the thermal state `e^{-βH} / Tr e^{-βH}`: agreement with `gibbsState`, unitary covariance
#print axioms STUProof.thermalState_diag
#print axioms STUProof.thermalState_conj

-- spectral theorem with sorted eigenvalues
#print axioms STUProof.exists_sorted_diagonalization
#print axioms STUProof.exists_thermalState_eq_conj

-- the STU conjecture for every Hermitian Hamiltonian
#print axioms STUProof.stu_exists_hermitian
