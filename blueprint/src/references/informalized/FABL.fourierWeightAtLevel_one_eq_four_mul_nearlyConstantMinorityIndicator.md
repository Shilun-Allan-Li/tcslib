<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.fourierWeightAtLevel_one_eq_four_mul_nearlyConstantMinorityIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minority indicator level-one weight

**Claim.** The level-one Fourier weight of $f$ is four times that of its nearly constant minority indicator.

**Proof.** Write level-one weight as the sum of squared singleton coefficients (`fourierWeightAtLevel_one_eq_sum_singleton`). For each coordinate, the singleton coefficient of the minority indicator is either $-\widehat f(\{i\})/2$ or $\widehat f(\{i\})/2$, according to the sign of the mean (`fourierCoeff_nearlyConstantMinorityIndicator_singleton`). In either case its square is $\widehat f(\{i\})^2/4$. Summing over coordinates gives the claimed factor of four.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.fourierCoeff_nearlyConstantMinorityIndicator_singleton`.
