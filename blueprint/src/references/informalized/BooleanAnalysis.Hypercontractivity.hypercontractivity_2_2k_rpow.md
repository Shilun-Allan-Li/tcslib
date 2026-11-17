<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: BooleanAnalysis.Hypercontractivity.hypercontractivity_2_2k_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-Power Hypercontractivity Bound

**Claim.** For every natural number $k\ge1$, if $\rho^2\le 1/(2k-1)$, then the $2k$-moment of the noise operator applied to $f$, raised to the power $1/(2k)$, is at most the square-moment norm of $f$.

**Proof.** Apply the integer-moment inequality `hypercontractivity_2_2k` to bound the $2k$-moment of the noisy function by the $k$th power of the second moment of $f$. Both quantities are nonnegative: the right-hand moment is nonnegative by `expect_sq_nonneg`, and the left-hand moment is the expectation of a square, since $(T_\rho f)^{2k}=((T_\rho f)^k)^2$. The map $u\mapsto u^{1/(2k)}$ is increasing on nonnegative reals, so applying it to the moment inequality gives the desired comparison. The exponents simplify using $k\ge1$, yielding the square-moment norm on the right and the stated $1/(2k)$ power on the left.

**Key facts.** `BooleanAnalysis.Hypercontractivity.hypercontractivity_2_2k`, `BooleanAnalysis.Hypercontractivity.expect_sq_nonneg`.
