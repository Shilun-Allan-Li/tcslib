<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_depthTwoFinishDifferent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Count for the Different-Value Completion

**Claim.** For the combined completion procedure, the query count equals the count spent in the third tree plus the count for the appropriate comparison tree, with the remaining tree queried only when the preceding evaluation does not match the third tree's value.

**Proof.** The procedure first runs $E_3$. The query-count rule for composing trees on disjoint coordinate sets says that the total is the first tree's count plus the continuation's count (`FiniteDecisionTree.queryCount_thenOnDisjoint`). If $E_3$ evaluates to $x_1$, the continuation runs $C_1(x_1)$; when that tree evaluates to the same value, it stops, and otherwise it also runs $C_2(x_2)$. If $E_3$ does not evaluate to $x_1$, the continuation instead runs $C_2(x_2)$ and runs $C_1(x_1)$ only if the evaluation of $C_2(x_2)$ fails to match the value of $E_3$. In both branches, mapping the final output does not change query counts (`FiniteDecisionTree.queryCount_mapOutput`), and the casts that reconcile coordinate-set descriptions likewise leave the count unchanged (`FiniteDecisionTree.queryCount_castAvailable`). These two cases give the displayed formula.

**Key facts.** `FABL.FiniteDecisionTree.queryCount_castAvailable`, `FABL.FiniteDecisionTree.queryCount_thenOnDisjoint`, `FABL.FiniteDecisionTree.queryCount_mapOutput`.
