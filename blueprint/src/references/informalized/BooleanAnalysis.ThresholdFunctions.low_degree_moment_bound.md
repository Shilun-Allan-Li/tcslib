<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.low_degree_moment_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree moment bound

**Claim.** For a coefficient family supported on subsets of size at most $k$ and $1<t<2$, its squared coefficient norm multiplied by $(t-1)^k$ is bounded by the $2/t$ power of the $t$-th absolute moment of its polynomial.

**Proof.** Set $\rho=\sqrt{t-1}$. The assumptions $1<t<2$ imply $0\le\rho\le1$, and $\rho\le\sqrt{(t-1)/(2-1)}$. Apply the one-function hypercontractivity inequality with input exponent $t$, output exponent $2$, and noise parameter $\rho$ (`general_one_function_hypercontractivity`), to the function given by the polynomial evaluation. It bounds the square-root of the noise-smoothed second moment by the $1/t$ power of the original $t$-th absolute moment. Both sides are nonnegative (`expect_sq_noiseOp_nonneg`, `expect_rpow_abs_nonneg`), so squaring preserves the inequality and yields the moment with exponent $2/t$. Finally, the degree lower bound for the noise-smoothed second moment says that it is at least $\rho^{2k}$ times the squared coefficient norm (`noise_degree_lower`). Since $\rho^{2k}=(t-1)^k$, combining these inequalities proves the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.general_one_function_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.expect_sq_noiseOp_nonneg`, `BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg`, `BooleanAnalysis.ThresholdFunctions.noise_degree_lower`.
