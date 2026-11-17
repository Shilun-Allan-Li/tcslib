<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.randomizedDecisionTreeComplexity_nand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND Decision-Tree Complexity

**Claim.** The randomized decision-tree complexity of NAND on two signs is $2$.

**Proof.** Let the admissible costs be the worst-case costs of zero-error randomized decision trees computing NAND. The exhibited tree has worst-case cost $2$ (\texttt{nandRandomizedTree\_worstCaseCost}), so the infimum of the admissible costs is at most $2$. For the reverse inequality, consider the input on which both signs are $-1$. Every such tree has expected query cost exactly $2$ on this input (\texttt{RandomizedDecisionTree.inputCost\_nandAllTrue\_eq\_two}), and its worst-case cost is at least its cost on that input (\texttt{RandomizedDecisionTree.inputCost\_le\_worstCaseCost}). Thus every admissible cost is at least $2$, so their infimum is at least $2$. The admissible costs are bounded below, as also follows from nonnegativity of worst-case cost (\texttt{RandomizedDecisionTree.worstCaseCost\_nonneg}), and the two inequalities yield the result.

**Key facts.** `FABL.RandomizedDecisionTree.worstCaseCost_nonneg`, `FABL.nandRandomizedTree_worstCaseCost`, `FABL.RandomizedDecisionTree.inputCost_nandAllTrue_eq_two`, `FABL.RandomizedDecisionTree.inputCost_le_worstCaseCost`.
