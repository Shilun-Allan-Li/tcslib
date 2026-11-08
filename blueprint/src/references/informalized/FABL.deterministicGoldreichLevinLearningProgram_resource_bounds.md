<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearningProgram_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Learner Resource Bounds

**Claim.** Every hypothesis-cost pair that has positive probability under the deterministic Goldreich–Levin learner uses zero random examples, no more than the query budget, and no more than the work budget.

**Proof.** The execution theorem identifies the learner’s distribution with a point mass at the deterministic query program’s output-cost pair (`runWithCost_deterministicGoldreichLevinLearningProgram`). Hence any pair in the distribution’s support equals that deterministic pair. The deterministic learner’s resource bound (`deterministicGoldreichLevinLearner_resource_bounds`) gives zero random examples and the stated query and work limits.

**Key facts.** `FABL.runWithCost_deterministicGoldreichLevinLearningProgram`, `FABL.deterministicGoldreichLevinLearner_resource_bounds`.
