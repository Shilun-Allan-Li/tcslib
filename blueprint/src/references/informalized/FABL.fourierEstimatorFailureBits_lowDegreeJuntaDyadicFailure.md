<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.fourierEstimatorFailureBits_lowDegreeJuntaDyadicFailure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dyadic Failure-Bit Count

**Claim.** For every natural number $b$, the failure-bit count at $\delta=1/2^{b+1}$ is exactly $b+2$.

**Proof.** At this parameter, the quantity inside the outer ceiling is $2/(1/2^{b+1})=2^{b+2}$, an integer. Thus its ceiling is $2^{b+2}$. The ceiling base-$2$ logarithm of this power of $2$ is its exponent, so the failure-bit count is $b+2$.

**Key facts.** `FABL.lowDegreeJuntaDyadicFailure_value`.
