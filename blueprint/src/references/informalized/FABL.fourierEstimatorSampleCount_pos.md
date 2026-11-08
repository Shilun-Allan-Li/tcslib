<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.fourierEstimatorSampleCount_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Sample Count

**Claim.** For $\varepsilon,\delta\in(0,1/2]$, the sample count $m=\lceil 2b(\delta)/\varepsilon^2\rceil$ is positive.

**Proof.** The failure-bit count $b(\delta)$ is positive, and $\varepsilon^2>0$. Thus $2b(\delta)/\varepsilon^2>0$. The ceiling of a positive number is at least $1$, so $m>0$.

**Key facts.** `FABL.fourierEstimatorFailureBits_pos`.
