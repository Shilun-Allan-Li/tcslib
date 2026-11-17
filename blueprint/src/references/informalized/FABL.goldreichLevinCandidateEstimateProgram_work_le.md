<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinCandidateEstimateProgram_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate estimator work bound

**Claim.** Every supported outcome of the candidate-estimation program has work cost at most eight times one more than its sample count, multiplied by one more than the dimension.

**Proof.** The candidate-estimation program is the scheduled restricted Fourier weight estimator followed by a map that packages its estimate into a record. Its run law is therefore the image of the estimator’s run law, with the cost unchanged (`LearningProgram.runWithCost_map`). Membership in the mapped support gives a supported estimator outcome. For that outcome, the cost identity for the restricted Fourier weight estimator identifies its cost exactly with the estimator’s prescribed cost (`restrictedFourierWeightEstimatorProgram_cost_eq`). The work component of this prescribed cost is at most $8(m+1)(n+1)$ (`restrictedFourierWeightEstimatorCost_work_le`). Taking $m$ to be the sample count associated with the specified accuracy and confidence yields the stated bound.

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.restrictedFourierWeightEstimatorProgram_cost_eq`, `FABL.restrictedFourierWeightEstimatorCost_work_le`.
