<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.fourierEstimatorFailureBits_le_sampleExponent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Bits and Sample Exponent

**Claim.** For learning parameters $\varepsilon,\delta\in(0,1/2]$, the failure-bit count $b$ is at most $N\varepsilon^2/2$, where $N=\lceil 2b/\varepsilon^2\rceil$.

**Proof.** By the defining property of the ceiling, $2b/\varepsilon^2\le N$. Since $\varepsilon^2\ge0$, multiplying gives $2b\le N\varepsilon^2$; division by $2$ proves the claim.
