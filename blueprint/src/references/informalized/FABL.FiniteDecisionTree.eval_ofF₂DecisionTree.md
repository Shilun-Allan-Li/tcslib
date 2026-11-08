<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.eval_ofF₂DecisionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the binary tree conversion

**Claim.** Evaluating the finite decision tree over $\mathbb{Z}/2\mathbb{Z}$ obtained from a binary decision tree gives the same label as evaluating the original binary tree.

**Proof.** Proceed by induction on the binary tree. At a leaf, both evaluations return the stored label. At a query of coordinate $i$, split into the two cases $x_i=0$ and $x_i\ne 0$. In the first case, the converted tree selects its zero child, and the original tree does too; the induction hypothesis for that child gives equal evaluations. In the second case, both select the one child, and its induction hypothesis gives the equality.
