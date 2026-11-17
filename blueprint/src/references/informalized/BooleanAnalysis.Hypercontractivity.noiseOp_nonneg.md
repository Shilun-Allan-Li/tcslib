<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.noiseOp_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Preserves Nonnegativity

**Claim.** If $0\le\rho\le1$ and $f$ is pointwise nonnegative, then $T_\rho f$ is pointwise nonnegative.

**Proof.** At each point $x$, express the noise operator as the finite sum $\sum_y K_\rho(x,y)f(y)$ (`noiseOp_eq_kernel_sum`). Each kernel weight is nonnegative when $0\le\rho\le1$ (`noiseKernel_nonneg`), and each value $f(y)$ is nonnegative by hypothesis. Every summand, and therefore their sum, is nonnegative.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noiseOp_eq_kernel_sum`, `BooleanAnalysis.Hypercontractivity.noiseKernel_nonneg`.
