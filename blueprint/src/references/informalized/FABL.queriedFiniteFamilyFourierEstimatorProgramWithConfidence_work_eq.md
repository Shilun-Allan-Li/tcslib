<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Fourier Estimator Work

**Claim.** Every possible outcome of the confidence-parameter finite-family Fourier estimator has charged local work exactly $|\mathcal F|Mn+|\mathcal F|M+|\mathcal F|M(n+1)$, where $M$ is the sample count per coefficient.

**Proof.** The exact-cost identity for every supported outcome (`queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq`) identifies its entire cost record with the estimator's prescribed cost. Taking the work component of that record yields the three charged contributions: $|\mathcal F|M n$ for processing coordinates, $|\mathcal F|M$ for the additional per-sample charge, and $|\mathcal F|M(n+1)$ for the explicitly charged local computation. Thus the outcome's work is exactly their sum.

**Key facts.** `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq`.
