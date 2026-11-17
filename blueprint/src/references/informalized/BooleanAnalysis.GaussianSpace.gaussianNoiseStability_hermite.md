<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoiseStability_hermite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite expansion of Gaussian noise stability

**Claim.** For $f$ in $L^2$ under the product standard Gaussian measure and $\rho\in[-1,1]$, Gaussian noise stability is the sum over multi-indices $\alpha$ of $\rho^{|\alpha|}$ times the squared Hermite coefficient of $f$.

**Proof.** Write $T_\rho f$ for the Gaussian noise operator applied to $f$. The $L^2$ preservation theorem for this operator (\texttt{gaussianNoise\_memLp}) ensures that both $f$ and $T_\rho f$ lie in the space where Hermite Plancherel applies. By the Plancherel identity for the Hermite coefficients (\texttt{hermite\_plancherel}), the stability integral $\int f\,T_\rho f$ equals the sum over $\alpha$ of the product of the two corresponding coefficients. The coefficient identity for Gaussian noise (\texttt{hermiteCoeff\_gaussianNoise}) says that the coefficient of $T_\rho f$ at $\alpha$ is $\rho^{|\alpha|}$ times that of $f$. Substitution makes each summand $\rho^{|\alpha|}(\operatorname{hermiteCoeff}(f,\alpha))^2$, yielding the claimed expansion.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianNoise_memLp`, `BooleanAnalysis.GaussianSpace.hermite_plancherel`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_gaussianNoise`.
