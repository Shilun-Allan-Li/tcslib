<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support of an Orthogonal Vector

**Claim.** If a vector is orthogonal to every vector vanishing on $S$, then each coordinate where it is nonzero belongs to $S$.

**Proof.** Take a coordinate $i$ outside $S$. The unit vector supported at $i$ vanishes on every coordinate in $S$, so it belongs to the coordinate-zero subspace (`mem_coordinateZeroSubspace_iff`). Orthogonality then says the given vector has dot product zero with this unit vector (`mem_perpendicularSubspace_iff`). Dotting with the unit vector extracts its $i$th coordinate (`f₂DotProduct_f₂UnitVector`), so that coordinate is zero. Therefore no coordinate outside $S$ belongs to the vector's support, using the characterization of support membership by nonzero coordinates (`mem_f₂Support`).

**Key facts.** `FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff`, `FABL.mem_perpendicularSubspace_iff`, `FABL.F₂DecisionTree.f₂DotProduct_f₂UnitVector`, `FABL.mem_f₂Support`.
