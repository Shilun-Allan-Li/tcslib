<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.polynomial_abs_third_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third Moment Bound

**Claim.** Under the stated independence, hypercontractivity, mean, variance, and degree assumptions, the third absolute moment of the random-input evaluation of $F$ is at most $(1/\rho)^{3k}(\sum_S F(S)^2)^{3/2}$.

**Proof.** The squared real $L^3$ norm of the evaluation is at most $(1/\rho)^{2k}\sum_S F(S)^2$ by the three-norm bound for multilinear polynomials (`polynomial_three_norm_sq`). Its evaluation belongs to $L^3$: each coordinate belongs to $L^3$ by hypercontractivity, and finite independent multilinear evaluations preserve this integrability (`evalMultilinearRV_memLp_nat`). Apply the third-moment-versus-norm inequality (`third_moment_le_of_three_norm_sq`) with $B=(1/\rho)^{2k}\sum_S F(S)^2$, which is nonnegative. This gives the desired bound after distributing the power $3/2$ across the product and simplifying $( (1/\rho)^{2k})^{3/2}=(1/\rho)^{3k}$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp_nat`, `BooleanAnalysis.GaussianSpace.Invariance.polynomial_three_norm_sq`, `BooleanAnalysis.GaussianSpace.Invariance.third_moment_le_of_three_norm_sq`.
