<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.spectralSparsityGranularity_exactSparseSpectrumSparsityBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Granularity at the Exact Sparsity Bound

**Claim.** For every nonnegative integer $k$, the spectral sparsity granularity at $2^{k+1}$ equals the degree Fourier granularity at $k+1$.

**Proof.** By definition, spectral sparsity granularity at $s$ is degree Fourier granularity at the integer logarithm of $s$ to base $2$. For $s=2^{k+1}$, this logarithm is $k+1$, since $2>1$. Substitution gives the claimed equality.
