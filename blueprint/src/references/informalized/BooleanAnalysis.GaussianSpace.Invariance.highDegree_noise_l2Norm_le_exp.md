<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceTruncation.lean :: BooleanAnalysis.GaussianSpace.Invariance.highDegree_noise_l2Norm_le_exp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# High-degree noise norm bound

**Claim.** If a Boolean-cube function has variance at most $1$, then for $0\le\delta\le1$ and $k\ge0$, the $L^2$ norm of the noise-smoothed part of degrees above $\lfloor k\rfloor$ is at most $\exp(-\delta k)$.

**Proof.** Put $\rho=1-\delta$, so $0\le\rho$. Whenever $k\le m$, the standard inequality $1-\delta\le e^{-\delta}$ gives $\rho^m\le e^{-\delta m}\le e^{-\delta k}$, using $\delta\ge0$. By Parseval (parseval), the squared norm of the high-degree part is the sum over sets $S$ with $\lfloor k\rfloor<|S|$ of $((1-\delta)^{|S|}\widehat f(S))^2$; the high-degree coefficient formula (KKL.fourierCoeff_highDegreePart) and the noise multiplier formula (BooleanAnalysis.noiseOp_fourier) identify these coefficients. For each such $S$, the floor property gives $k\le |S|$, so the preceding power bound shows its squared contribution is at most $e^{-2\delta k}\widehat f(S)^2$. These sets are nonempty. The variance identity expressing variance as the sum of squared nonconstant Fourier coefficients (BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier) therefore bounds the total by $e^{-2\delta k}\operatorname{Var}(f)\le e^{-2\delta k}$. Taking square roots yields the claim, since the exponential is positive.

**Key facts.** `BooleanAnalysis.parseval`, `KKL.fourierCoeff_highDegreePart`, `BooleanAnalysis.noiseOp_fourier`, `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`.
