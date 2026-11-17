<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Berry–Esseen Bound for Rademacher Tails

**Claim.** For every real threshold $t$ and natural number $m$, the upper-tail probability of the normalized Rademacher sum in dimension $m+1$ differs from the standard Gaussian upper-tail probability by at most $2C$ times the normalized coefficient, where $C$ is the third-moment Berry–Esseen constant.

**Proof.** Use the uniform measure on the sign cube as a probability space, and take the coordinate summands of the normalized Rademacher sum as random variables. Each summand is measurable and square-integrable (`hammingBallRademacherSummand_memLp`); the summands are independent (`hammingBallRademacherSummands_iIndep`), have mean zero (`integral_hammingBallRademacherSummand_eq_zero`), and their variances sum to one (`variance_hammingBallRademacherSummand`, `sum_normalizedRademacherCoefficient_sq`). Each summand has absolute value equal to the normalized coefficient, using the fact that a sign has value $-1$ or $1$ (`signValue_eq_neg_one_or_one`) and that the coefficient is nonnegative (`normalizedRademacherCoefficient_nonneg`). The third-moment sum is consequently at most that coefficient (`sum_integral_abs_cube_le_of_ae_abs_le`).

Apply the interval Berry–Esseen estimate to the interval above $t$ (`exercise5_16_interval`). The event probability under the chosen measure equals the uniform sign-cube probability (`hammingBallUniformMeasure_real_event`), and the Gaussian measure of that interval equals the standard Gaussian upper tail (`standardGaussianUpperTail_eq_measureReal_Ioi`). Finally, the expected tail indicator equals the same uniform event probability (`expect_hammingUpperTailIndicator_eq_uniformProbability`). Substituting these identifications into the interval estimate yields the asserted bound.

**Key facts.** `FABL.hammingBallRademacherSummand_memLp`, `FABL.hammingBallRademacherSummands_iIndep`, `FABL.integral_hammingBallRademacherSummand_eq_zero`, `FABL.sum_normalizedRademacherCoefficient_sq`, `FABL.variance_hammingBallRademacherSummand`, `FABL.normalizedRademacherCoefficient_nonneg`, `FABL.signValue_eq_neg_one_or_one`, `FABL.sum_integral_abs_cube_le_of_ae_abs_le`, `FABL.exercise5_16_interval`, `FABL.hammingBallUniformMeasure_real_event`, `FABL.standardGaussianUpperTail_eq_measureReal_Ioi`, `FABL.expect_hammingUpperTailIndicator_eq_uniformProbability`.
