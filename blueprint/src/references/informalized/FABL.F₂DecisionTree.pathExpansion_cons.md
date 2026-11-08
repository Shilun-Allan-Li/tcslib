<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.pathExpansion_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path Expansion over a Cons

**Claim.** For a path followed by a finite list of real-output paths, the expansion is the sum of the first path’s output times its indicator and the expansion of the remaining list.

**Proof.** Evaluate both sides at an arbitrary vector $x$. The list map over a cons has first term $\mathrm{path.output}\,\mathrm{path.indicator}(x)$ followed by the mapped terms from the tail. The sum of these terms is the first term plus the tail sum, which is exactly the asserted equality at $x$. Since the functions agree at every $x$, they are equal.
