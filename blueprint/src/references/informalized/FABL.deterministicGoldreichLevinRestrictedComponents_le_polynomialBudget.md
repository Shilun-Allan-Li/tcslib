<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinRestrictedComponents_le_polynomialBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted component budget bounds

**Claim.** For the restricted-weight input associated with a deterministic Goldreich–Levin input, the construction work, stage query budget, and restricted local work are each bounded by its polynomial budget.

**Proof.** Take the full coordinate set $J$ and let $S$ contain every coordinate in $J$. The restricted-weight resource bound ( `deterministicRestrictedWeightCost_resource_bounds`) gives both a query bound and a total-work bound by the polynomial budget for this choice. By the query-cost identity ( `deterministicRestrictedWeightCost_queries`), the cost's query count is the product of the outer and inner sample counts; this is exactly the stage query budget, so the second claimed bound follows. For the work bound, expand total work using the work decomposition ( `deterministicRestrictedWeightCost_work`): it is construction work plus query count plus local work. Since $S$ contains all coordinates, its size is $n$, and its local work is exactly the restricted local work in the claim. Thus the resource bound controls the sum of the three nonnegative quantities, and hence controls each one individually by the same polynomial budget.

**Key facts.** `FABL.deterministicRestrictedWeightCost_resource_bounds`, `FABL.deterministicRestrictedWeightCost_queries`, `FABL.deterministicRestrictedWeightCost_work`.
