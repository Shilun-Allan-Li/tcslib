<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.monotoneBoundedInfluenceRandomExampleProgram_cost_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bounds on Program Costs

**Claim.** Under the stated hypotheses, every supported outcome uses at most $K(C,Q)(n+1)^{E(C,Q)}$ random examples, makes zero membership queries, and has work at most $W(C,Q)(n+1)^{F(C,Q)}$, with the specified constants and exponents.

**Proof.** First, the program cost bound (`monotoneBoundedInfluenceRandomExampleProgram_cost_le`) bounds each supported outcome by the random-example and work budgets and gives zero queries. Apply the fixed-power budget estimate (`monotoneBoundedInfluenceRandomExampleBudget_le_fixed_power`) to the example count, and the corresponding work-budget estimate (`monotoneBoundedInfluenceWorkBudget_le_fixed_power`) to the work count. Transitivity of the inequalities gives the two asserted polynomial bounds, and the query count remains zero.

**Key facts.** `FABL.monotoneBoundedInfluenceRandomExampleProgram_cost_le`, `FABL.monotoneBoundedInfluenceRandomExampleBudget_le_fixed_power`, `FABL.monotoneBoundedInfluenceWorkBudget_le_fixed_power`.
