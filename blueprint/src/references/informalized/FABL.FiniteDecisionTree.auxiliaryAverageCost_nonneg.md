<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.auxiliaryAverageCost_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Auxiliary Average Cost

**Claim.** The auxiliary average cost of $T$ under the product distribution is nonnegative.

**Proof.** By definition, the auxiliary average cost is the probability-mass-function expectation of the query count. For every input, the query count is a list length, hence a natural number and therefore nonnegative as a real number. The nonnegativity of expectation for a pointwise nonnegative function (`FABL.pmfExpectation_nonneg`) now gives the result.

**Key facts.** `FABL.pmfExpectation_nonneg`.
