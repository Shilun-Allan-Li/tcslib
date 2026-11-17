<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.biasedQueryScore_replaceCoordinate_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Score Invariance Under an Unused Coordinate Change

**Claim.** Replacing a coordinate unavailable to the tree leaves its biased query score unchanged.

**Proof.** The original input and the input with coordinate $j$ replaced agree at every available coordinate. The tree's query trace is therefore unchanged (`FABL.FiniteDecisionTree.queryTrace_eq_of_agreeOn`), so its queried-coordinate set is unchanged as well. Every coordinate in that set belongs to the available set (`FABL.FiniteDecisionTree.queryTrace_subset_available`), and hence differs from $j$. The replacement consequently leaves the input value at each coordinate contributing to the score unchanged. The summands, and thus the biased query score, are equal.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_eq_of_agreeOn`, `FABL.FiniteDecisionTree.queryTrace_subset_available`.
