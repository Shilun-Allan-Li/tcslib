<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.worstCaseCost_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of worst-case cost

**Claim.** For a randomized decision tree over a finite nonempty input alphabet, the worst-case expected number of queries is nonnegative.

**Proof.** Choose any input by taking the same element of the nonempty alphabet in every coordinate. The expected query count on this input is nonnegative (`inputCost_nonneg`). The worst-case cost is the supremum of the input costs, so it is at least the cost at this particular input. Therefore the worst-case cost is nonnegative.

**Key facts.** `FABL.RandomizedDecisionTree.inputCost_nonneg`.
