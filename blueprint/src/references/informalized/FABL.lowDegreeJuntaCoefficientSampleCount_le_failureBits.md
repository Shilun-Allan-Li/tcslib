<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaCoefficientSampleCount_le_failureBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Sample Count Bound

**Claim.** The coefficient sample count for accuracy $1/(3\cdot2^k)$ and confidence $\gamma=\delta/(4|\mathcal F|)$ is at most $36\cdot4^k$ times the number of failure bits associated with $\gamma$.

**Proof.** The sample-count estimate (\(\texttt{FABL.fourierEstimatorSampleCount_cast_le}\)) bounds the sample count, viewed as a rational number, by $4$ times the failure-bit count divided by the square of the accuracy. Substituting the accuracy $1/(3\cdot2^k)$ makes this expression $4\cdot(3\cdot2^k)^2$ times the failure-bit count, which equals $36\cdot4^k$ times that count. Since both sides are natural numbers, the rational inequality gives the asserted natural-number bound.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`.
