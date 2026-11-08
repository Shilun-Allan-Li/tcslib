<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinCandidateEstimateProgram_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate Estimate Failure Probability

**Claim.** For any target, threshold, coordinate set $J$, and frequency prefix $P$, the probability that the candidate-estimation program's record is inaccurate is at most its call-confidence parameter.

**Proof.** The candidate program maps the scheduled weight-estimator's rational output to a record with fixed coordinate set $J$ and prefix $P$. The probability of failure after this mapping equals the probability that the estimator's output lies in the preimage of the inaccurate-record event (`LearningProgram.runWithCost_map`, together with the standard support-measure identity for a mapped probability distribution). Unfolding the record's accuracy condition, this preimage is exactly the event that the absolute estimation error is at least the chosen accuracy parameter, which here is $\tau^2/4$. The scheduled estimator's failure bound limits this event's probability by its confidence parameter; applying it with the prescribed accuracy and call-confidence parameters proves the result (`scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le`).

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le`.
