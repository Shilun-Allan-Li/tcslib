<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualSpectralSparsity_eq_spectralSparsity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of spectral sparsities

**Claim.** The number of nonzero vector Fourier coefficients of $f$ equals the number of nonzero Fourier coefficients indexed by linear functionals on $\mathbb F_2^n$.

**Proof.** The vector space duality map gives a bijection between vectors $\gamma\in\mathbb F_2^n$ and linear functionals. Under this bijection, corresponding Fourier coefficients agree (\texttt{FABL.dualFourierCoeff_vectorDualEquiv}). Hence a functional has a nonzero coefficient exactly when its corresponding vector does. The proof maps the dual Fourier support back to the vector Fourier support and verifies injectivity and surjectivity using the inverse duality map. Therefore the supports have equal cardinality; the vector spectral sparsity is identified with that support cardinality by \texttt{FABL.spectralSparsity_eq_card_vectorFourierSupport}. The support membership criteria are \texttt{FABL.mem_dualFourierSupport} and \texttt{FABL.mem_vectorFourierSupport}.

**Key facts.** `FABL.spectralSparsity_eq_card_vectorFourierSupport`, `FABL.mem_dualFourierSupport`, `FABL.mem_vectorFourierSupport`, `FABL.dualFourierCoeff_vectorDualEquiv`.
