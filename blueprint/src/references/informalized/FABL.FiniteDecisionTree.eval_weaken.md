<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.eval_weaken -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under Enlarged Availability

**Claim.** If $A\subseteq B$, then viewing a finite decision tree with available coordinates $A$ as a tree with available coordinates $B$ does not change its evaluation on any input.

**Proof.** Proceed by induction on the tree, allowing the larger set $B$ to vary. At a leaf, weakening leaves the label unchanged, so the evaluations agree. At a query of coordinate $i$, weakening keeps the same query and weakens each child from $A\setminus\{i\}$ to $B\setminus\{i\}$. On input $x$, both trees choose the child indexed by $x_i$; the induction hypothesis for that child says their evaluations agree.
