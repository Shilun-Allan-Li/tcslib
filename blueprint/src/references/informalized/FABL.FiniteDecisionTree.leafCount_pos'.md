<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.leafCount_pos' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Leaf Count

**Claim.** Every finite decision tree over a finite, nonempty query alphabet has at least one leaf.

**Proof.** Induct on the tree. A leaf has leaf count $1$, which is positive. At a query node, the leaf count is the sum of the leaf counts of its children, one for each alphabet element. By induction each summand is positive, and the alphabet is nonempty, so this finite sum is positive.
