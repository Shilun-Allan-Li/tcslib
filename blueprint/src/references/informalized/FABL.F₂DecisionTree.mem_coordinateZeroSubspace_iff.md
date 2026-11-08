<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Coordinate Zero Subspace

**Claim.** A vector belongs to the kernel of restriction to a coordinate set exactly when all its coordinates in that set are zero.

**Proof.** If $x$ lies in the kernel, its restriction is the zero function. Evaluating that function at any coordinate in the set shows that the corresponding coordinate of $x$ is zero. Conversely, suppose every coordinate of $x$ in the set is zero. The restriction of $x$ then agrees with the zero function at every element of its domain, so it is the zero function and $x$ lies in the kernel.
