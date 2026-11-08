<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearningProgram_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning and resource guarantee

**Claim.** Every possible outcome of the deterministic Goldreich–Levin learning program has classification error at most the input accuracy, uses no random examples, and has query count and local work bounded by the stated polynomial runtime bound.

**Proof.** First, the accuracy theorem for this program gives the relative Hamming distance bound for the output hypothesis (\(`deterministicGoldreichLevinLearningProgram_relativeHammingDist_le`\)). The resource theorem says that the same outcome uses zero random examples and that its query count and local work are at most the corresponding integer budgets (\(`deterministicGoldreichLevinLearningProgram_resource_bounds`\)). Regard the latter two inequalities as real inequalities by casting their natural-number quantities to the reals. The query-budget and work-budget comparison theorems bound each cast budget by the polynomial runtime bound (\(`queryBudget_cast_le_polynomialRuntimeBound`\), \(`workBudget_cast_le_polynomialRuntimeBound`\)); transitivity gives both required real-valued resource bounds. Combining these three conclusions proves the claim.

**Key facts.** `FABL.deterministicGoldreichLevinLearningProgram_relativeHammingDist_le`, `FABL.deterministicGoldreichLevinLearningProgram_resource_bounds`, `FABL.DeterministicGoldreichLevinInput.queryBudget_cast_le_polynomialRuntimeBound`, `FABL.DeterministicGoldreichLevinInput.workBudget_cast_le_polynomialRuntimeBound`.
