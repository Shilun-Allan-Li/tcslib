<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.variance_hammingBallRademacherSummand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Normalized Coordinate Sign

**Claim.** For each coordinate, the variance of its sign value multiplied by the normalized coefficient is the square of that coefficient.

**Proof.** The summand has mean zero, by the preceding integral computation for this coordinate (`integral_hammingBallRademacherSummand_eq_zero`). Hence its variance is the integral of its square. Under the uniform measure on the sign cube, this integral is the uniform expectation (`integral_uniformPMF_eq_expect`). At every point, the coordinate sign is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), so squaring the summand gives the constant equal to the square of the normalized coefficient. The expectation of a constant is that constant, proving the formula.

**Key facts.** `FABL.integral_hammingBallRademacherSummand_eq_zero`, `FABL.integral_uniformPMF_eq_expect`, `FABL.signValue_eq_neg_one_or_one`.
