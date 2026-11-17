<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.coordinateSubcube_eq_binaryAffineSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate subcubes are affine subspaces

**Claim.** The set of vectors agreeing with a base point on the selected coordinates is the affine subspace obtained by translating the coordinate-zero subspace by that base point.

**Proof.** Take any vector $x$. Membership in the translated subspace is equivalent to $x$ plus the base point belonging to the coordinate-zero subspace (`mem_binaryAffineSubspace_iff_add_mem`). Membership in that zero subspace means that $x_i+a_i=0$ at every selected coordinate (`mem_coordinateZeroSubspace_iff`). If $x_i=a_i$, this sum is zero because every element of $\mathbb F_2$ is its own additive inverse. Conversely, if the sum is zero, then $x_i=-a_i=a_i$, again because negation is the identity in $\mathbb F_2$. Hence the two sets agree.

**Key facts.** `FABL.mem_binaryAffineSubspace_iff_add_mem`, `FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff`.
