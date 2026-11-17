<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.worstCaseCost_ofDeterministic_le_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic cost bounded by depth

**Claim.** When a deterministic decision tree computing \(f\) is viewed as a randomized tree with a single deterministic choice, its worst-case expected query count is at most its depth.

**Proof.** For every input, the deterministic tree’s expected query count equals its query count on that input (`inputCost_ofDeterministic`). The query count on any input is at most the tree’s depth (`FiniteDecisionTree.queryCount_le_depth`). Hence every input cost is at most the depth, and so their supremum, the worst-case cost, is also at most the depth.

**Key facts.** `FABL.RandomizedDecisionTree.inputCost_ofDeterministic`, `FABL.FiniteDecisionTree.queryCount_le_depth`.
