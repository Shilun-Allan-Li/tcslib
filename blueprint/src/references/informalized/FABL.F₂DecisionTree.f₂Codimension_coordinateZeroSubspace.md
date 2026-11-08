<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Codimension of a Coordinate-Zero Subspace

**Claim.** The dimension of the orthogonal complement of the subspace of vectors vanishing on a coordinate set $S$ is $|S|$.

**Proof.** The coordinate restriction map sends a vector to its values on $S$, and it is surjective (`coordinateRestriction_surjective`). The rank–nullity formula therefore says that the dimension of its kernel plus the dimension of its range is $n$. Its range is the entire space of functions on $S$, whose dimension is $|S|$, so the kernel has dimension $n-|S|$. The dimension of the orthogonal complement of a subspace is $n$ minus the dimension of that subspace (`finrank_perpendicularSubspace`). Applying this to the coordinate-zero subspace, which is the kernel of the restriction map, gives $n-(n-|S|)=|S|$.

**Key facts.** `FABL.F₂DecisionTree.coordinateRestriction_surjective`, `FABL.finrank_perpendicularSubspace`.
