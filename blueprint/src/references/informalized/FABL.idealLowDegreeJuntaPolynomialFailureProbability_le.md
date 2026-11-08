<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.idealLowDegreeJuntaPolynomialFailureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial learner failure probability

**Claim.** If the encoded restricted Boolean function has algebraic degree at most the prescribed polynomial degree, the probability that the low-degree polynomial learner fails to recover it exactly is at most one quarter of the failure parameter.

**Proof.** View the prescribed batch as independent uniform inputs to the restricted cube, and reindex those inputs as points of a cube whose dimension is the number of free coordinates. The input-row map sends a uniform batch to a uniform batch of the required polynomial-learner sample size (`map_uniformPMF_lowDegreeJuntaPolynomialInputRow`). Under this reindexing, the restricted labels are precisely the labels of the reindexed restricted function; this identifies the failure event with the event that the polynomial learner on the reindexed cube outputs the wrong encoded function (`lowDegreeJuntaPolynomialHypothesis_ideal`).

For that learner, failure is contained in its separation-failure event whenever the target's algebraic degree is at most the learner's degree (`lowDegreeF₂PolynomialLearner_failure_subset_separationFailure`). The scheduled sample bound gives probability at most the chosen quarter-failure parameter for this separation event (`measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le`). Transferring this bound through the uniform input-row map yields the same bound for failure under the original batch law. Since the quarter-failure parameter equals one quarter of the given parameter, this is the claimed estimate.

**Key facts.** `FABL.map_uniformPMF_lowDegreeJuntaPolynomialInputRow`, `FABL.lowDegreeJuntaPolynomialHypothesis_ideal`, `FABL.lowDegreeF₂PolynomialLearner_failure_subset_separationFailure`, `FABL.measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le`.
