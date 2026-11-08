<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Fourier-Estimator Query Count

**Claim.** Every possible outcome of the confidence-parameter finite-family Fourier estimator uses exactly $|\mathcal F|M$ membership queries, where $M$ is the prescribed number of samples per coefficient.

**Proof.** The exact-cost theorem says every supported outcome has cost equal to the estimator’s prescribed cost (`queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq`). By the definition of that cost, its query coordinate is $|\mathcal F|$ times the prescribed sample count. This is the asserted exact count.

**Key facts.** `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq`.
