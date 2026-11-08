<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.Path.expect_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Path Indicator

**Claim.** Under the uniform probability measure on the binary cube, the expected indicator of a path’s cylinder is $2^{-\ell}$, where $\ell$ is the number of coordinates assigned by the path.

**Proof.** First express the expectation of the path indicator as its Fourier coefficient at the zero vector (`FABL.vectorFourierCoeff_eq_expect`); at zero, the Walsh character contributes the constant factor one. The indicator is also the indicator of the affine subspace obtained by translating the coordinate-zero subspace on the path’s support by its base vector (`FABL.F₂DecisionTree.Path.indicator_eq_binaryAffineSubspace`). The zero vector belongs to the perpendicular subspace, so the Fourier coefficient formula for an affine-subspace indicator applies: at such a frequency, the coefficient is the Walsh character at the base vector times the inverse cardinality of the perpendicular subspace (`FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem`). At zero frequency the character is one, leaving that inverse cardinality. The inverse perpendicular cardinality for this coordinate-zero subspace equals the inverse path size, which is $2^{-\ell}$ (`FABL.F₂DecisionTree.Path.inversePerpendicularCard_coordinateZeroSubspace`).

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.F₂DecisionTree.Path.indicator_eq_binaryAffineSubspace`, `FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem`, `FABL.F₂DecisionTree.Path.inversePerpendicularCard_coordinateZeroSubspace`.
