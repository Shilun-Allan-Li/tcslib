<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.exists_unique_singletonCoeff_sq_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration of level-one Fourier weight

**Claim.** If a Boolean function has level-one Fourier weight one, one singleton coefficient has square one and every other singleton coefficient vanishes.

**Proof.** The level-one weight equals the sum of the squares of the singleton coefficients (`fourierWeightAtLevel_one_eq_sum_singleton`), so this sum is one. At each coordinate, the square of the singleton coefficient is either zero or one when the level-one weight is one (`singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtLevel_one_eq_one`). If every coordinate had square zero, their sum would be zero, contradicting that it is one. Choose a coordinate $i$ whose square is one. Removing its term from the sum leaves a sum of squares equal to zero. Every term in that remaining sum is nonnegative, so each is zero; in particular, for every $j\ne i$, the square of the $j$th coefficient is zero, and hence that coefficient itself is zero.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtLevel_one_eq_one`.
