<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean :: BooleanAnalysis.ThresholdFunctions.expect_mul_linear_form -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlation with a Linear Form

**Claim.** For a real-valued function on the Boolean cube and real coefficients indexed by coordinates, its expected product with the corresponding linear form is the sum of each coefficient times the singleton Fourier coefficient of the function.

**Proof.** Expand the linear form inside the expectation and distribute the finite sums, then interchange the sums over cube points and coordinates. For each fixed coordinate, the character indexed by its singleton set equals the sign of that coordinate (BooleanAnalysis.chiS_singleton). Hence the inner sum over cube points is precisely the singleton Fourier coefficient, multiplied by the chosen coefficient; summing over coordinates gives the formula.

**Key facts.** `BooleanAnalysis.chiS_singleton`.
