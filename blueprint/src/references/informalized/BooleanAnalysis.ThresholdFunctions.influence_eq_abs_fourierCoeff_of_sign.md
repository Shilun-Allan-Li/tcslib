<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.influence_eq_abs_fourierCoeff_of_sign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of a unate coordinate

**Claim.** If a $\pm1$-valued function has discrete derivative in coordinate $i$ with a fixed sign, then its influence in that coordinate equals the absolute value of its singleton Fourier coefficient.

**Proof.** Rewrite the influence as the expectation of the squared discrete derivative, and rewrite the singleton Fourier coefficient as the expectation of that derivative. Since the function is $\pm1$-valued, the square of the derivative equals its absolute value (`derivative_sq_eq_abs_of_pmOne`). If the derivative is everywhere nonnegative, its absolute value is itself, so both quantities are the same nonnegative expectation. If it is everywhere nonpositive, its absolute value is its negation. The Fourier coefficient is then the negative of the expectation of the derivative, by linearity of expectation (`expect_neg`), and is nonpositive; its absolute value is that same nonnegative quantity. Nonnegativity of the relevant expectations follows from `expect_nonneg`.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.influence_eq_expect_derivative_sq`, `BooleanAnalysis.ThresholdFunctions.fourierCoeff_singleton_eq_expect_derivative`, `BooleanAnalysis.ThresholdFunctions.derivative_sq_eq_abs_of_pmOne`, `BooleanAnalysis.ThresholdFunctions.expect_neg`, `BooleanAnalysis.ThresholdFunctions.expect_nonneg`.
