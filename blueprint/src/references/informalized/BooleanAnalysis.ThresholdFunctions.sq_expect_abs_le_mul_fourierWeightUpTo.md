<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.sq_expect_abs_le_mul_fourierWeightUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Fourier Weight Bound

**Claim.** If a polynomial has degree at most $k$ and represents $f$ by thresholding, then the square of its mean absolute value is at most its coefficient square sum times the Fourier weight of $f$ up to degree $k$.

**Proof.** Because $f$ is the threshold sign of the polynomial, at every point the product of the polynomial value and $f$ equals the absolute value of the polynomial value, including when that value is zero. Thus the mean absolute value is the inner product of the polynomial with $f$. Expanding the polynomial in its characters expresses this inner product as the sum over subsets $S$ of the coefficient $p(S)$ times the Fourier coefficient of $f$ at $S$. For subsets with $|S|>k$, the polynomial coefficient vanishes; hence this sum can be written using only degrees at most $k$. Cauchy–Schwarz bounds its square by the product of the sum of squared polynomial coefficients and the sum of squared Fourier coefficients through degree $k$, which is the stated Fourier weight.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.expect_abs_eval_eq_innerProduct`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.innerProduct_eval`.
