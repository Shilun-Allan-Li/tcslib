<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.eval_queryCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Coordinate Query Tree

**Claim.** Querying the coordinates in $L$ in order, branching on their values in $x$, and then using the tree selected by the resulting assignment evaluates to the same value as applying the finishing function to the seed updated with $x$ on $L$ and evaluating that tree at $x$.

**Proof.** Induct on the list $L$, allowing the seed to vary. For the empty list, the queried-coordinate tree is simply the finishing tree at the seed, and the assignment is unchanged. For a list beginning with coordinate $j$, the query branches according to whether $x_j=0$. In the zero case, the recursive tree uses the seed updated at $j$ to zero; this agrees with updating the seed using $x_j$, so the induction hypothesis identifies the branch evaluation with the claimed finishing-tree evaluation. In the other case, since $x_j$ is a bit, it equals $1$. The one branch uses the seed updated at $j$ to one, again agreeing with the update by $x_j$, and the induction hypothesis gives the same conclusion.
