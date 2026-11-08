<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Estimator Work Bound

**Claim.** For every possible outcome of the confidence-parameter finite-family Fourier estimator, the charged local work, viewed as a rational number, is at most the stated bound in terms of the family size, dimension, failure-bit count, and accuracy.

**Proof.** The exact-work identity for every supported outcome (`queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_eq`) expresses the work as the sum of three terms, each involving the family size and the sample count $M$. Algebraically, that sum is $2|\mathcal F|(n+1)M$. The sample-count estimate (`queriedFiniteFamilySamplesPerCoefficient_cast_le`) gives $M\le 16|\mathcal F|^2L/\varepsilon^2$. Since $|\mathcal F|$ and $n+1$ are nonnegative, multiplying this inequality by $2|\mathcal F|(n+1)$ preserves its direction. The result is the claimed bound, with constant $2\cdot16=32$ and family-size factor $|\mathcal F|^3$.

**Key facts.** `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_eq`, `FABL.queriedFiniteFamilySamplesPerCoefficient_cast_le`.
