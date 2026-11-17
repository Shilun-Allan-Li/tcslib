<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinStageEstimateProgram_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage Work Bound

**Claim.** Every possible stage outcome has charged work at most the number of candidates times $8(m+1)(n+1)$, where $m$ is the estimator sample count at the specified parameters.

**Proof.** The stage program sequences one candidate-estimation program for each candidate. Each such program has charged work at most $8(m+1)(n+1)$ (`goldreichLevinCandidateEstimateProgram_work_le`). Work is additive across a sequence, and the cost-projection bound therefore limits total work by the sequence length times this per-program bound (`LearningProgram.costProjection_le_of_mem_support_sequence`). The sequence length is the number of candidates, yielding the claimed inequality.

**Key facts.** `FABL.LearningProgram.costProjection_le_of_mem_support_sequence`, `FABL.goldreichLevinCandidateEstimateProgram_work_le`.
