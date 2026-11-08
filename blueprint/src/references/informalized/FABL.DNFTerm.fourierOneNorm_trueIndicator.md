<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFTerm.fourierOneNorm_trueIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier one norm of a term indicator

**Claim.** For every conjunction term, the Fourier one norm of its indicator function is $1$.

**Proof.** First identify the term’s indicator on the Boolean cube with the indicator of an affine subspace: the subspace fixes the coordinates in the term’s support, and its base point records the required signs (FABL.DNFTerm.trueIndicator_binaryCubeSignEquiv). The Fourier one norm equals the spectral $1$-norm after translating between sign vectors and Boolean vectors (FABL.fourierOneNorm_eq_spectralPNorm_one). Finally, the spectral $1$-norm of the indicator of any such affine subspace is $1$ (FABL.spectralPNorm_one_setIndicator_binaryAffineSubspace). Combining these identities proves the claim.

**Key facts.** `FABL.fourierOneNorm_eq_spectralPNorm_one`, `FABL.DNFTerm.trueIndicator_binaryCubeSignEquiv`, `FABL.spectralPNorm_one_setIndicator_binaryAffineSubspace`.
