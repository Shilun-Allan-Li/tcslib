<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinCandidateEstimateProgram_queries_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate estimator query count

**Claim.** Every supported outcome of the candidate-estimation program has query cost exactly twice its sample count, with the accuracy and confidence parameters specified by the threshold.

**Proof.** The candidate-estimation program first runs the scheduled restricted Fourier weight estimator and then converts its numerical output into an estimate record. The law of this mapped program is the image of the estimator’s outcome law under the map that forms the record, while preserving its cost (`LearningProgram.runWithCost_map`). Thus any supported mapped outcome comes from a supported estimator outcome, with the same cost. The scheduled estimator uses the sample count determined by the given accuracy and confidence parameters, and its query-count theorem says each supported outcome costs exactly twice that count (`scheduledRestrictedFourierWeightEstimatorProgram_queries_eq`). Applying this with accuracy `goldreichLevinWeightAccuracy τ` and confidence `goldreichLevinCallConfidence n τ` proves the claim.

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.scheduledRestrictedFourierWeightEstimatorProgram_queries_eq`.
