<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.averageCost_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Average Query Cost

**Claim.** For a finite input alphabet, every randomized decision tree and every probability distribution on that alphabet have nonnegative average query cost.

**Proof.** For each fixed input, the input cost is the seed-law expectation of the number of queries made by the selected deterministic tree. Query counts are nonnegative, so this expectation is nonnegative (`inputCost_nonneg`). The average cost is then the expectation of these input costs under the product input distribution; an expectation of a pointwise nonnegative function is nonnegative (`pmfExpectation_nonneg`).

**Key facts.** `FABL.RandomizedDecisionTree.inputCost_nonneg`, `FABL.pmfExpectation_nonneg`.
