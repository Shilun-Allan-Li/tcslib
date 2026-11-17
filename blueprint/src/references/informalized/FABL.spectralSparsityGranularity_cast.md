<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.spectralSparsityGranularity_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real form of spectral sparsity granularity

**Claim.** For every nonnegative integer $s$, the real cast of the spectral sparsity granularity equals $2(2^{-1})^{\operatorname{log}_2 s}$, where the logarithm is the integer logarithm to base $2$.

**Proof.** By definition, the spectral sparsity granularity at $s$ is the degree Fourier granularity evaluated at $\operatorname{Nat.log} 2\,s$. Apply the real-cast formula for degree Fourier granularity (\(\texttt{degreeFourierGranularity\_cast}\)) at this integer. Its right-hand side is $2(2^{-1})^{\operatorname{Nat.log} 2\,s}$, as required.

**Key facts.** `FABL.degreeFourierGranularity_cast`.
