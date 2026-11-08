<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_increment_variance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise increment variance

**Claim.** For correlations $\rho,\sigma\in[-1,1]$, the sum of the two increment variances equals the variance associated with correlation $\rho\sigma$.

**Proof.** If $r\in[-1,1]$, then $1-r^2\ge0$, so the square of $\sqrt{1-r^2}$ is $1-r^2$. The product $\rho\sigma$ also lies in $[-1,1]$ (\texttt{correlation\_mul\_mem}), so this square-root identity applies to all three terms. The left-hand side therefore becomes $\sigma^2(1-\rho^2)+(1-\sigma^2)$, while the right-hand side becomes $1-\rho^2\sigma^2$. Expanding the left-hand side gives the same expression.

**Key facts.** `BooleanAnalysis.GaussianSpace.correlation_mul_mem`.
