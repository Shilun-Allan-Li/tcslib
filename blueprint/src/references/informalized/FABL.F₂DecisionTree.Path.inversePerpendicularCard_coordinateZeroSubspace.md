<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.inversePerpendicularCard_coordinateZeroSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal size of the orthogonal complement

**Claim.** For the subspace of vectors vanishing on the coordinates specified by a path, the reciprocal of $2$ raised to the dimension of its orthogonal complement is $2^{-k}$, where $k$ is the number of specified coordinates.

**Proof.** The codimension identity for the coordinate-zero subspace (`codimension_coordinateZeroSubspace_eq_length`) identifies the dimension of its orthogonal complement with the path length $k$. Substitute this identity into the definition of the reciprocal perpendicular cardinality; the result is exactly the definition of the inverse path size, namely $2^{-k}$.

**Key facts.** `FABL.F₂DecisionTree.Path.codimension_coordinateZeroSubspace_eq_length`.
