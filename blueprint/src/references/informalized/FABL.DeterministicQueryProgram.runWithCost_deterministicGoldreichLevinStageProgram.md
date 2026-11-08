<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of a Goldreich–Levin Stage

**Claim.** For an eligible stage and finite active family, running the deterministic Goldreich–Levin stage with the target as oracle returns its prescribed estimate records and incurs exactly the prescribed cost: one batch of restricted-weight queries and the stage’s charged local work.

**Proof.** Unfold the stage program and the recursive definition of running with cost. The program asks one batch of restricted-weight queries, with the prescribed query points. Its continuation receives the oracle answers, charges the stage’s prescribed local work, and returns the estimate records computed from those answers. The run therefore returns the same records as the definition that substitutes the target’s answers at each query point. Its cost is the batch’s query cost plus the local-work charge, which is exactly the defined stage cost.
