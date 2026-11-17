<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinSecondStage_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-Stage Resource Bounds

**Claim.** For every admissible learning input, Boolean target, and query state, the second-stage program uses zero random examples, makes at most the coefficient sample count in membership queries, and uses at most its coefficient work budget in local work.

**Proof.** Split according to whether the query state's active family is absent. If it is absent, the second-stage program returns the empty hypothesis without querying or charging work, so all three bounds follow from nonnegativity of the budgets. If an active family is present, split again according to whether its size is within the active cap. When it is, the stage is exactly the coefficient program, whose resource theorem (`deterministicGoldreichLevinCoefficientProgram_resource_bounds`) gives zero random examples, exactly the coefficient query budget, and work at most the coefficient work budget; weakening query equality to an upper bound gives the claim. When the family exceeds the cap, the program again returns the empty hypothesis without queries or work, and the three bounds follow as in the absent-family case.

**Key facts.** `FABL.deterministicGoldreichLevinCoefficientProgram_resource_bounds`.
