<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productMean_abs_laplacian_rpow_le_two_rpow_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Laplacian Moment Bound

**Claim.** For a sign-valued function on the product space, the expected $p$th power of the absolute coordinate Laplacian is at most $2^p$ times its influence at that coordinate, for every $p\ge 1$.

**Proof.** First, rewrite the product mean of the absolute Laplacian moment as the product mean of the coordinate conditional absolute moment, using the equality between those two quantities (`productMean_abs_laplacian_rpow_eq_conditional`). Next, express the influence as the product mean of the coordinate conditional variance (`productInfluence_eq_expect_coordinateConditionalVariance`). Unfolding these conditional quantities reduces the desired comparison, at each fixed choice of the other coordinates, to a one-coordinate estimate. For such a fixed choice $x$, let $g(\omega)$ be the value of $f$ when coordinate $i$ is replaced by $\omega$. Since $f$ takes values in $\{-1,1\}$, so does $g$. The sign-valued moment estimate (`pmfExpectation_abs_sub_mean_rpow_le_two_rpow_mul_sq`) bounds the expected $p$th power of $|g-\mathbb E g|$ by $2^p$ times the expected square $(g-\mathbb E g)^2$. Integrate this pointwise inequality over the remaining product coordinates; monotonicity of expectation preserves it. Pulling the constant $2^p$ outside the expectation (`pmfExpectation_const_mul`) gives the claimed bound in terms of the influence.

**Key facts.** `FABL.FiniteFourierBasis.productMean_abs_laplacian_rpow_eq_conditional`, `FABL.FiniteFourierBasis.productInfluence_eq_expect_coordinateConditionalVariance`, `FABL.pmfExpectation_abs_sub_mean_rpow_le_two_rpow_mul_sq`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_mono`.
