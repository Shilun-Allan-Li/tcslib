<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.inputCost_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Input Cost

**Claim.** For every input, the expected number of queries made by a zero-error randomized decision tree is nonnegative.

**Proof.** For each seed, a query count is a nonnegative integer, and hence is nonnegative as a real number. The expectation of a pointwise nonnegative function under a probability mass function is nonnegative (`pmfExpectation_nonneg`).

**Key facts.** `FABL.pmfExpectation_nonneg`.
