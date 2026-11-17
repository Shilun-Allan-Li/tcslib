<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinCandidateEstimateProgram_outerFailureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate estimator failure bound

**Claim.** For any target, threshold, coordinate set, and frequency prefix, the outer probability that the candidate estimate is inaccurate is at most the program’s call-confidence parameter.

**Proof.** The probability bound for the event under the program’s ordinary outcome law is at most the call-confidence parameter, by the candidate-estimator failure estimate (`goldreichLevinCandidateEstimateProgram_failureProbability_le`). The outer event probability is finite, by `LearningProgram.outerEventProbability_ne_top`, so the standard comparison between a finite nonnegative extended-real number and a real bound reduces the desired inequality to the corresponding inequality for its real value. That real value equals the ordinary event probability by `LearningProgram.outerEventProbability_toReal`. Substituting the failure estimate gives the result.

**Key facts.** `FABL.LearningProgram.outerEventProbability_ne_top`, `FABL.LearningProgram.outerEventProbability_toReal`, `FABL.goldreichLevinCandidateEstimateProgram_failureProbability_le`.
