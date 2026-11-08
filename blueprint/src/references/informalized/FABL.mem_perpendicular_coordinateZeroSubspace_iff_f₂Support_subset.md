<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DegreeOneWeight.lean :: FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perpendicularity and Support

**Claim.** A vector over $\mathbb F_2$ is perpendicular to the subspace of vectors vanishing on a coordinate set $C$ if and only if its support is contained in $C$.

**Proof.** For the forward implication, apply the fact that every vector perpendicular to the coordinate zero subspace has support contained in the specified coordinates (`f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace`). For the reverse implication, take any vector $x$ in the coordinate zero subspace. Its dot product with $\gamma$ is the sum of $x_i$ over the support of $\gamma$ (`f₂DotProduct_eq_coordinateSum_f₂Support`). Each such support coordinate lies in $C$ by hypothesis, and $x_i=0$ there because $x$ lies in the coordinate zero subspace (`mem_coordinateZeroSubspace_iff`). Hence every summand vanishes, so the dot product is zero. Since this holds for every vector in the subspace, the characterization of perpendicular membership (`mem_perpendicularSubspace_iff`) gives the desired perpendicularity.

**Key facts.** `FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace`, `FABL.f₂DotProduct_eq_coordinateSum_f₂Support`, `FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff`, `FABL.mem_perpendicularSubspace_iff`.
