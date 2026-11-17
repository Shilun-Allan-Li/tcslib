<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.eval_pushEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under Coordinate Embedding

**Claim.** Evaluating a decision tree after embedding its queried coordinates along an injection gives the same result as evaluating the original tree on the input restricted along that injection.

**Proof.** Proceed by induction on the tree. If the tree is a leaf, both evaluations return its stored value. If its root queries coordinate $i$, the embedded tree queries $e(i)$. Both evaluations therefore choose the zero child exactly when $x_{e(i)}=0$, and otherwise choose the one child. In either case, the induction hypothesis for that child identifies its evaluation on $x$ with the original child’s evaluation on the input $j\mapsto x_{e(j)}$.
