<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.restrictedFourierWeight_eq_mean_fixedReindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Weight as a Fixed-Cube Mean

**Claim.** The restricted Fourier weight equals the average, over fixed assignments on the coordinates outside $J$, of the squared Fourier coefficient of the corresponding restriction at $S$.

**Proof.** First, the Fourier expansion identity for restricted weight expresses it as the sum over frequencies on the fixed coordinates of the squared ambient Fourier coefficients. The companion identity in `restrictedFourierWeight_equation6_6` identifies that sum with the mean over all assignments on the fixed-coordinate cube of the squared restricted Fourier coefficient at $S$. The theorem uses these two identities in sequence. It then reindexes the uniform mean from the fixed-coordinate cube to the standard sign cube of dimension equal to the number of fixed coordinates: the equivalence `fixedSignCubeEquiv` preserves the uniform average, and the summand is exactly the same after this change of variables.

**Key facts.** `FABL.restrictedFourierWeight_equation6_6`.
