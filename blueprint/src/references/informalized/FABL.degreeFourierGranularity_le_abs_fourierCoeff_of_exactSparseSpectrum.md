<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.degreeFourierGranularity_le_abs_fourierCoeff_of_exactSparseSpectrum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Granularity lower bound

**Claim.** Under the stated sparsity bound, every nonzero Fourier coefficient of the Boolean function has absolute value at least the Fourier granularity at level $k+1$.

**Proof.** The sparsity hypothesis gives Fourier granularity: there is an integer $z$ such that the coefficient at $U$ is $z$ times the granularity at level $k+1$ (`isFourierGranular_toReal_of_exactSparseSpectrumSparsity`). Since the coefficient is nonzero and the granularity is positive, $z$ cannot be zero. Thus $|z|ge 1$. Taking absolute values in the coefficient identity and using positivity of the granularity yields the claimed lower bound.

**Key facts.** `FABL.isFourierGranular_toReal_of_exactSparseSpectrumSparsity`, `FABL.degreeFourierGranularity_pos`.
