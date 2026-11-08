<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.RandomizedDecisionTree.outputConditionalCost_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Conditional Query Cost

**Claim.** For every output value, the maximum conditional query cost—using zero on inputs with a different output—is nonnegative.

**Proof.** Choose any input in the nonempty input space. If its output is the specified value, its expected query cost is nonnegative (`RandomizedDecisionTree.inputCost_nonneg`); otherwise the assigned value is zero. The maximum over all inputs is at least this particular value, so it too is nonnegative.

**Key facts.** `FABL.RandomizedDecisionTree.inputCost_nonneg`.
