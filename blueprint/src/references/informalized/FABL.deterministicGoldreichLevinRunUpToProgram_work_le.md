<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinRunUpToProgram_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Stage Work Bound

**Claim.** For every admissible learning input, Boolean target, and $k$ no greater than the dimension, the work used by the deterministic Goldreich–Levin program through stage $k$ is at most $k$ times its per-stage work budget.

**Proof.** Use the cost-projection bound for the run with the projection that extracts local work. This projection vanishes on zero cost and is additive. To verify its per-stage hypothesis, consider a stage whose active family is within the active cap. Each active frequency contributes at most two candidates, so the candidate set has size at most twice the active-family size (`card_goldreichLevinCandidates_le_two_mul`). Multiplying this inequality by the per-candidate restricted local work bounds the stage's local-work charge. Adding the controller work and query-budget charge gives at most the stated stage-work budget. The run-level projection bound then yields the claimed bound of $k$ times that budget.

**Key facts.** `FABL.deterministicGoldreichLevinRunUpToProgram_costProjection_le`, `FABL.card_goldreichLevinCandidates_le_two_mul`.
