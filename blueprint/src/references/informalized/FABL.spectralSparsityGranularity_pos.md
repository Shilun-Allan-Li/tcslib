<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.spectralSparsityGranularity_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of Spectral Sparsity Granularity

**Claim.** For every nonnegative integer $s$, the spectral sparsity granularity at $s$ is strictly positive.

**Proof.** The spectral sparsity granularity at $s$ is, by definition, the degree Fourier granularity at $\operatorname{Nat.log}(2,s)$. The degree Fourier granularity is strictly positive for every integer input, so applying that fact at $\operatorname{Nat.log}(2,s)$ proves the result.

**Key facts.** `FABL.degreeFourierGranularity_pos`.
