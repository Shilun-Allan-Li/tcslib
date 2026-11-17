<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictionWeights.lean :: FABL.fourierCoeff_restrictionFourierCoeff_comp_fixedSignCubeEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient Under Cube Reindexing

**Claim.** Reparametrizing the fixed-coordinate cube by its finite-coordinate equivalence carries the Fourier coefficient at $T$ to the indexed Fourier coefficient at the transported frequency.

**Proof.** The two coefficients are expectations over cubes with equivalent coordinate sets. Change variables along the equivalence from the ordinary finite cube to the fixed-coordinate cube; this preserves the uniform average. Under this change of variables, the character indexed by $T$ becomes the indexed character on the image of $T$ under the inverse coordinate equivalence. The equality of these characters follows by mapping the factors in their defining products coordinate by coordinate, so the integrands agree.
