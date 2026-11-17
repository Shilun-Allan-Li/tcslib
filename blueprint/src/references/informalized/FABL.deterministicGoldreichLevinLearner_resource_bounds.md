<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearner_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learner Resource Bounds

**Claim.** The deterministic Goldreich–Levin learner uses zero random examples, makes no more than its specified query budget, and performs no more than its specified work budget.

**Proof.** View the learner as the first-stage program followed by the second-stage program applied to the first stage’s output. The run-with-cost law for sequential programs says that the total cost is the sum of these two stage costs (`runWithCost_bind`). The first-stage resource theorem bounds its random examples by zero, its queries by the list-stage budget, and its work by the list-stage budget (`deterministicGoldreichLevinProgram_resource_bounds`). The second-stage resource theorem gives zero random examples and bounds its queries and work by their coefficient-stage budgets (`deterministicGoldreichLevinSecondStage_resource_bounds`). Adding the two zero-example counts gives zero; adding the query bounds gives the learner’s total query budget, and adding the work bounds gives its total work budget, by the definitions of those combined budgets.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_bind`, `FABL.deterministicGoldreichLevinProgram_resource_bounds`, `FABL.deterministicGoldreichLevinSecondStage_resource_bounds`.
