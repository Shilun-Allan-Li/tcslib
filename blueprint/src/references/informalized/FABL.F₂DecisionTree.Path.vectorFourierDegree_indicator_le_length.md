<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.vectorFourierDegree_indicator_le_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier degree of a path indicator

**Claim.** The Fourier degree of the indicator of the set of inputs matching a path is at most the number of coordinates fixed by that path.

**Proof.** Use the characterization of Fourier degree at most $k$: every coefficient indexed by a character whose support has more than $k$ coordinates must vanish (`FABL.vectorFourierDegree_le_iff`). Take $k$ to be the path length and consider any character whose support has size greater than this length. If its coefficient for the path indicator were nonzero, the path indicator's equality with the indicator of the affine subspace determined by its support and base point (`FABL.F₂DecisionTree.Path.indicator_eq_binaryAffineSubspace`), together with the nonvanishing criterion for an affine-subspace indicator (`FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff`), would place the character in the perpendicular subspace of the coordinate-zero subspace on the path support. The support-containment result for such a perpendicular subspace (`FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace`) then puts the character's support inside the path support. Its cardinality is consequently at most the path support's cardinality, which is the path length. This contradicts the chosen character's support size being larger. Thus all coefficients required by the degree characterization vanish, proving the bound.

**Key facts.** `FABL.vectorFourierDegree_le_iff`, `FABL.F₂DecisionTree.Path.indicator_eq_binaryAffineSubspace`, `FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff`, `FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace`.
