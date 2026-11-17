<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Noise.lean :: BooleanAnalysis.GaussianSpace.noiseOp_mem_unitInterval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range Preservation by the Noise Operator

**Claim.** If $f$ takes values in $[0,1]$ and $0\le\rho\le1$, then $T_\rho f(x)$ belongs to $[0,1]$ for every Boolean input $x$.

**Proof.** At a fixed input $x$, express the noise operator as the finite weighted sum $\sum_y K_\rho(x,y)f(y)$ (BooleanAnalysis.Hypercontractivity.noiseOp_eq_kernel_sum). Each weight is nonnegative (BooleanAnalysis.Hypercontractivity.noiseKernel_nonneg), and the weights sum to $1$ (BooleanAnalysis.Hypercontractivity.noiseKernel_sum_right). Each value $f(y)$ lies in the convex interval $[0,1]$. Therefore their weighted average lies in $[0,1]$, as required.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noiseOp_eq_kernel_sum`, `BooleanAnalysis.Hypercontractivity.noiseKernel_nonneg`, `BooleanAnalysis.Hypercontractivity.noiseKernel_sum_right`.
