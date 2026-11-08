<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier-Estimator Query Bound

**Claim.** Every possible outcome of the confidence-parameter finite-family Fourier estimator uses at most $16|\mathcal F|^3L/\varepsilon^2$ membership queries, where $L$ is the failure-bit count at confidence parameter $\delta/|\mathcal F|$.

**Proof.** For any supported outcome, the exact query-count result identifies its query count with $|\mathcal F|$ times the prescribed samples per coefficient (`queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_eq`). The sample-count bound gives, after viewing the natural-number count as rational, an upper bound of $16|\mathcal F|^2L/\varepsilon^2$ (`queriedFiniteFamilySamplesPerCoefficient_cast_le`). Multiply this inequality by the nonnegative quantity $|\mathcal F|$ and substitute the exact query count. The resulting expression is $16|\mathcal F|^3L/\varepsilon^2$, as required.

**Key facts.** `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_eq`, `FABL.queriedFiniteFamilySamplesPerCoefficient_cast_le`.
