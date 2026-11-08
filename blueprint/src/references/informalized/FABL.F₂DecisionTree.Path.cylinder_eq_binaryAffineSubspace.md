<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.cylinder_eq_binaryAffineSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path Cylinders Are Affine Subspaces

**Claim.** The set of binary vectors agreeing with every value fixed by a path is the affine subspace formed by adding the path’s base vector to the subspace of vectors vanishing on its support.

**Proof.** Take a vector $x$. The path-matching characterization says that $x$ matches the path exactly when $x_i$ equals the base vector at every coordinate $i$ in the support (`FABL.F₂DecisionTree.Path.matches_iff_forall_mem_support_eq_base`). Membership in the affine subspace based at the path’s base vector is equivalent to the sum of $x$ and that base vector lying in the coordinate-zero subspace (`FABL.mem_binaryAffineSubspace_iff_add_mem`). Membership in that subspace, in turn, means that this sum vanishes on every supported coordinate (`FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff`). In characteristic two, adding the same value to itself gives zero, so matching implies this vanishing. Conversely, if the sum vanishes, then $x_i$ is the negative of the base value; every element of $\mathbb{F}_2$ is its own negative, so $x_i$ equals the base value and hence matches the path.

**Key facts.** `FABL.F₂DecisionTree.Path.matches_iff_forall_mem_support_eq_base`, `FABL.mem_binaryAffineSubspace_iff_add_mem`, `FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff`.
