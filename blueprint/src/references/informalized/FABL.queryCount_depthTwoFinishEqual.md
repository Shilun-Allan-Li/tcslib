<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_depthTwoFinishEqual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Count for the Equal-Value Completion

**Claim.** For the combined completion procedure, the query count equals the count spent in $C_1(x_1)$ plus the count of the continuation: if its evaluation equals $x_1$, the procedure runs $C_2(x_1)$ and runs $E_3$ only when that evaluation fails to match; otherwise it runs $E_3$ and then runs $C_2(x_1)$ only when $E_3$ fails to match.

**Proof.** The construction first runs $C_1(x_1)$, so the disjoint-tree composition rule gives its query count plus the count of the selected continuation (`FiniteDecisionTree.queryCount_thenOnDisjoint`). If $C_1(x_1)$ evaluates to $x_1$, the continuation runs $C_2(x_1)$. It stops when the latter's evaluation matches the value of $C_1(x_1)$; otherwise it runs $E_3$. If $C_1(x_1)$ does not evaluate to $x_1$, the continuation runs $E_3$ and adds $C_2(x_1)$'s count only if $E_3$ evaluates to a different value from $C_1(x_1)$. Output mapping does not alter a tree's query count (`FiniteDecisionTree.queryCount_mapOutput`), and changing the available-coordinate description by equality does not alter it either (`FiniteDecisionTree.queryCount_castAvailable`). The two cases therefore yield the claimed formula.

**Key facts.** `FABL.FiniteDecisionTree.queryCount_thenOnDisjoint`, `FABL.FiniteDecisionTree.queryCount_castAvailable`, `FABL.FiniteDecisionTree.queryCount_mapOutput`.
