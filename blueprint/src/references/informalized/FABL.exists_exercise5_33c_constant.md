<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.exists_exercise5_33c_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Approximation for Regular Thresholds

**Claim.** There is a positive constant $C$ such that, for every dimension, correlation parameter in $(-1,1)$, normalized coefficient vector with $|a_i|\le\varepsilon$, and pair of signs, the stated quadrant probability for the correlated weighted sum differs from the corresponding Gaussian probability by at most $C\varepsilon/\sqrt{1-\rho^2}$.

**Proof.** Start with the multivariate Bentkus bound for sums of independent, mean-zero, three-integrable random vectors and convex measurable sets, with a positive-definite covariance matrix. Apply it in dimension two to the coordinate summands of the correlated pair sum and to the sign quadrant. The summands are independent, have finite third moments, and have mean zero (`FABL.regularThresholdPairSummand_iIndep`, `FABL.regularThresholdPairSummand_memLp`, and `FABL.integral_regularThresholdPairSummand_eq_zero`). The quadrant is measurable and convex (`FABL.measurableSet_signQuadrant`, `FABL.isConvexSet_signQuadrant`), and the covariance matches the matrix with diagonal entries $1$ and off-diagonal entries $\rho$ (`FABL.covarianceBilin_regularThresholdPairSum`). This matrix is positive definite for $-1<\rho<1$ (`FABL.correlationMatrix_posDef`), so Bentkus's estimate bounds the probability difference by its constant times the sum of the third moments after applying the inverse square root of the covariance matrix. Finally, the whitening-moment estimate bounds that sum by $4\varepsilon/\sqrt{1-\rho^2}$ (`FABL.sum_integral_regularThresholdPairSummand_whitening_cube_le`). Multiplying the constants gives the claimed bound, with the positive choice $4C(2)^{1/4}$.

**Key facts.** `FABL.regularThresholdPairSummand_memLp`, `FABL.regularThresholdPairSummand_iIndep`, `FABL.integral_regularThresholdPairSummand_eq_zero`, `FABL.correlationMatrix_posDef`, `FABL.covarianceBilin_regularThresholdPairSum`, `FABL.measurableSet_signQuadrant`, `FABL.isConvexSet_signQuadrant`, `FABL.sum_integral_regularThresholdPairSummand_whitening_cube_le`.
