<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DegreeOneWeight.lean :: FABL.expect_setIndicator_coordinateSubcube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density of a coordinate subcube

**Claim.** The uniform expectation of the indicator of the coordinate subcube fixed by a set of coordinates is $2^{-k}$, where $k$ is the number of those coordinates.

**Proof.** Identify the coordinate subcube with the affine subspace obtained by translating the coordinate-zero subspace by the given base point (`coordinateSubcube_eq_binaryAffineSubspace`). The expectation of its indicator is the zero-frequency vector Fourier coefficient: the Fourier coefficient is the expectation of the function times the zero Walsh character (`vectorFourierCoeff_eq_expect`), and that character is constantly one. Since zero belongs to the perpendicular subspace, the affine-subspace Fourier coefficient formula gives this coefficient as the Walsh character at the base point times the inverse perpendicular-subspace cardinality (`vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem`). The character at zero is one, and the coordinate-zero subspace has codimension equal to the number of fixed coordinates (`f₂Codimension_coordinateZeroSubspace`); hence the inverse perpendicular cardinality is $2^{-k}$.

**Key facts.** `FABL.F₂DecisionTree.coordinateSubcube_eq_binaryAffineSubspace`, `FABL.vectorFourierCoeff_eq_expect`, `FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem`, `FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace`.

**Caveat.** The supplied informal statement also lists broader affine-subspace Fourier claims, but the formal theorem and proof establish only the stated expectation for a coordinate subcube.
