<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.fourierEstimatorFailureBits_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Failure-Bit Count

**Claim.** For every $\delta\in(0,1/2]$, the failure-bit count is positive.

**Proof.** Since $\delta\le1/2<2$, we have $1<2/\delta$. The ceiling of $2/\delta$ is therefore greater than $1$. The ceiling base-$2$ logarithm of an integer greater than $1$ is positive, proving the claim.
