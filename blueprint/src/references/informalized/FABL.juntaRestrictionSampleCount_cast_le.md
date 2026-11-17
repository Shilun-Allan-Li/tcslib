<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaRestrictionSampleCount_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on the Sample Count

**Claim.** The rational cast of the junta restriction sample count is at most $2^{k+1}M+16\cdot4^k B(\delta)$, where $B(\delta)$ is the Fourier estimator failure-bit count.

**Proof.** Expand the sample count into its initial term $2^{k+1}M$ and the Fourier estimator sample count at the matching accuracy. The latter is at most $4B(\delta)/\varepsilon^2$ by `fourierEstimatorSampleCount_cast_le`. Here $\varepsilon=2^{-(k+1)}$, so $4/\varepsilon^2=4\cdot 2^{2k+2}=16\cdot4^k$. Substituting this bound and preserving the initial term gives the claimed inequality.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`.
