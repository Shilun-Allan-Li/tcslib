<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.spectralSparsity_ne_of_granularity_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral Sparsity Avoids Its Parameter

**Claim.** Let $n,s\in\mathbb N$ and let $f:\mathbb F_2^n\to\{\pm1\}$. If $1<s$ and $1<s\bigl(2(1/2)^{\lfloor\log_2 s\rfloor}\bigr)^2$, then the number of nonzero vector Fourier coefficients of its real-valued version is not $s$.

**Proof.** Suppose instead that the spectral sparsity of the real-valued version of $f$ equals $s$. Since $s>1$, the sparsity is greater than $1$, so the sparsity and granularity inequality (FABL.spectralSparsity_mul_granularity_sq_le_one) applies. Substituting the assumed equality into its bound gives $s$ times the square of the spectral sparsity granularity at $s$ at most $1$. This contradicts the hypothesis that the same quantity is greater than $1$. Hence the spectral sparsity cannot equal $s$.

**Key facts.** `FABL.spectralSparsity_mul_granularity_sq_le_one`.
