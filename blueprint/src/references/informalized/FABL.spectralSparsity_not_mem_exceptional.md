<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.spectralSparsity_not_mem_exceptional -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exceptional spectral sparsities

**Claim.** For every dimension and every sign-valued function on the binary cube, the number of nonzero vector Fourier coefficients is not any of $2,3,5,6,7,9$.

**Proof.** Suppose the spectral sparsity is one of the six listed values. Split into the corresponding six cases. For each of $2,3,5,6,7$, the spectral sparsity granularity bound rules out that value: at each such integer $s$, the hypotheses $1<s$ and $1<s\,\mathrm{granularity}(s)^2$ hold, so the general exclusion theorem gives spectral sparsity different from $s$ (`spectralSparsity_ne_of_granularity_bound`). In the remaining case, $s=9$, apply the separate exclusion of nine (`spectralSparsity_ne_nine`). Each case contradicts its assumed equality, so none of the six values can occur.

**Key facts.** `FABL.spectralSparsity_ne_of_granularity_bound`, `FABL.spectralSparsity_ne_nine`.
