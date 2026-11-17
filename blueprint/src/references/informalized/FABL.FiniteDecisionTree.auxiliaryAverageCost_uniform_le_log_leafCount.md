<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.auxiliaryAverageCost_uniform_le_log_leafCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Average Cost and Leaf Count

**Claim.** Under independent uniform sign-valued coordinates, a finite decision tree's average query count is at most the base-two logarithm of its number of leaves.

**Proof.** Proceed by induction on the tree. At a leaf, the query count is zero and the leaf count is one, so both sides are zero.

At a query node, the average-cost recurrence (`FABL.FiniteDecisionTree.auxiliaryAverageCost_query`) expresses its cost as one plus the average of the costs of the two children. Since the sign alphabet has exactly two elements, $1$ and $-1$, this average is their arithmetic mean. The induction hypotheses bound the two child costs by the logarithms of their leaf counts. Each child has positive leaf count (`FABL.FiniteDecisionTree.leafCount_pos'`), so the logarithmic inequality `FABL.one_add_average_logb_two_le_logb_two_add` bounds one plus the average of those logarithms by the logarithm of the sum of the two leaf counts. That sum is exactly the parent tree's leaf count. The uniform-expectation identity (`FABL.pmfExpectation_uniformPMF_eq_expect`) supplies the uniform averaging used in the recurrence; the constant expectation fact (`FABL.pmfExpectation_const`) handles the leaf case.

**Key facts.** `FABL.FiniteDecisionTree.auxiliaryAverageCost_query`, `FABL.FiniteDecisionTree.leafCount_pos'`, `FABL.one_add_average_logb_two_le_logb_two_add`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.pmfExpectation_const`.
