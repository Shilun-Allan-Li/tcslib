<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictionWeights.lean :: FABL.fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm after reindexing coefficients

**Claim.** The Fourier one-norm of the restriction Fourier coefficient, viewed as a function of the outside signs and reindexed by a cube of the same dimension, equals the sum of the absolute values of its Fourier coefficients indexed by subsets of the outside-coordinate set.

**Proof.** Reindex the sum defining the Fourier one-norm by the bijection between the coordinates of the cube of dimension equal to the number of outside coordinates and the outside-coordinate set. Under this bijection, finite coordinate subsets correspond to finite subsets of that set. For each subset, the Fourier coefficient of the reindexed function equals the corresponding indexed Fourier coefficient of the restriction Fourier coefficient function, by the coefficient identity (\texttt{fourierCoeff_restrictionFourierCoeff_comp_fixedSignCubeEquiv}). Taking absolute values and summing over the bijection proves the equality.

**Key facts.** `FABL.fourierCoeff_restrictionFourierCoeff_comp_fixedSignCubeEquiv`.
