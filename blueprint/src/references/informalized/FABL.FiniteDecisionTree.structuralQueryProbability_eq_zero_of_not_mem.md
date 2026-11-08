<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.structuralQueryProbability_eq_zero_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unavailable Coordinates Are Never Queried

**Claim.** If a coordinate is not among the available coordinates of a finite decision tree, its structural query probability, computed using the given probability mass function, is zero.

**Proof.** Proceed by induction on the tree. At a leaf, every structural query probability is zero by definition. At a query node, its queried coordinate belongs to the available set, so it cannot equal the coordinate assumed unavailable. The structural probability is therefore the expected structural probability of that coordinate in the child selected by the current alphabet value. Erasing the queried coordinate preserves its unavailability: anything available in the erased set was available before. By the induction hypothesis each child probability is zero. The expectation of this constant-zero function is zero, proving the claim.

**Key facts.** `FABL.pmfExpectation_const`.
