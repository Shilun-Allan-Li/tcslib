<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SparsePolynomialApproximation.lean :: FABL.polynomialSparsity_sampledFourierPolynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparsity of a sampled Fourier polynomial

**Claim.** The number of nonzero Fourier coefficients of the Fourier polynomial formed from the distinct sampled sets is at most the number $s$ of samples.

**Proof.** The Fourier coefficient of a sparse Fourier approximation at a frequency $T$ is its assigned coefficient when $T$ belongs to the defining family, and is zero otherwise (`fourierCoeff_sparseFourierApproximation`). Consequently, if a coefficient of the sampled polynomial is nonzero, its frequency must belong to the family of distinct sampled sets. The Fourier support is therefore contained in that family, so its cardinality is at most the family's cardinality. The family is the image of the $s$ sample indices under the sampling map, and an image of a finite set has cardinality at most that of its domain; thus the support has size at most $s$.

**Key facts.** `FABL.fourierCoeff_sparseFourierApproximation`, `FABL.mem_fourierSupport`.
