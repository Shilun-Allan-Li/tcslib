<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.spectralSparsity_mul_granularity_sq_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparsity and Granularity Inequality

**Claim.** For a sign-valued function whose real-valued version has spectral sparsity greater than $1$, its spectral sparsity $s$ times the square of the spectral sparsity granularity at $s$ is at most $1$.

**Proof.** Let $F(x)$ be the real value of the given sign-valued function, and let $s$ be its spectral sparsity. The granularity theorem for sign-valued functions (FABL.isVectorFourierGranular_signValue_spectralSparsity) says that every Fourier coefficient of $F$ is an integer multiple of the spacing $\varepsilon$, where $\varepsilon$ is the spectral sparsity granularity at $s$; the equivalence between granularity and integer multiples (FABL.isVectorFourierGranular_iff) makes this explicit. Positivity of the spacing follows from (FABL.spectralSparsityGranularity_pos). For any frequency in the Fourier support, its coefficient is nonzero, so its integer multiplier is nonzero. The absolute value of a nonzero integer is at least $1$, and consequently the square of that coefficient is at least $\varepsilon^2$. Summing over the support gives at least $s\varepsilon^2$, since the support has cardinality $s$ (FABL.spectralSparsity_eq_card_vectorFourierSupport). Parseval's identity for sign-valued functions says the sum of squares of all Fourier coefficients is $1$ (FABL.sum_sq_vectorFourierCoeff_signValue_eq_one). The sum over the support is no greater, because every omitted squared coefficient is nonnegative. Therefore $s\varepsilon^2\le 1$, as required.

**Key facts.** `FABL.isVectorFourierGranular_signValue_spectralSparsity`, `FABL.spectralSparsityGranularity_pos`, `FABL.isVectorFourierGranular_iff`, `FABL.spectralSparsity_eq_card_vectorFourierSupport`, `FABL.sum_sq_vectorFourierCoeff_signValue_eq_one`.
