<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandRandomizedTree_worstCaseCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Worst-case cost of the randomized NAND tree

**Claim.** The worst-case expected query cost of the specified randomized decision tree for the two-variable NAND function is $2$.

**Proof.** For every input, the formula for the input cost (`nandRandomizedTree_inputCost`) is the average of two terms, each at most $2$. Thus every input cost is at most $2$, and hence so is their supremum, the worst-case cost. For the reverse inequality, the input with both coordinates equal to $-1$ has cost $2$ (`RandomizedDecisionTree.inputCost_nandAllTrue_eq_two`); every individual input cost is bounded above by the worst-case cost (`RandomizedDecisionTree.inputCost_le_worstCaseCost`). The worst-case cost is therefore at least $2$, proving equality.

**Key facts.** `FABL.nandRandomizedTree_inputCost`, `FABL.RandomizedDecisionTree.inputCost_nandAllTrue_eq_two`, `FABL.RandomizedDecisionTree.inputCost_le_worstCaseCost`.
