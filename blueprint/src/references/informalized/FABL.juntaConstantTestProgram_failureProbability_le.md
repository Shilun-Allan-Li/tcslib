<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaConstantTestProgram_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta Test Failure Bound

**Claim.** If the target depends on at most $k$ coordinates, then for each allowed failure parameter $\delta$, the probability that the constant-testing program makes an incorrect decision is at most $\delta$.

**Proof.** First express the test program as the scheduled Fourier estimator followed by the decision rule. The run law of a mapped program is the image of the original law (`FABL.LearningProgram.runWithCost_map`), so the test's error probability equals the estimator's probability that the resulting estimate leads to an incorrect decision. By monotonicity of event probabilities (`FABL.LearningProgram.eventProbability_mono`), this is at most the probability that the estimate is not close enough to the true constant Fourier coefficient. Indeed, whenever the estimate is within the accuracy threshold, the decision rule is correct for a $k$-junta (`FABL.decideJuntaConstant_isCorrect_of_close`). Finally, the scheduled estimator's failure bound (`FABL.scheduledFourierCoeffEstimatorProgram_failureProbability_le`), applied to the empty set and the specified parameters, bounds that probability by $\delta$.

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.LearningProgram.eventProbability_mono`, `FABL.decideJuntaConstant_isCorrect_of_close`, `FABL.scheduledFourierCoeffEstimatorProgram_failureProbability_le`.
