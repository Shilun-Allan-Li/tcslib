<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_gaussianGenerator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficient of the Gaussian Generator

**Claim.** If $g$ is the Gaussian generator of $f$, then its Hermite coefficient at $\alpha$ is the total degree of $\alpha$ times the corresponding coefficient of $f$.

**Proof.** Consider, for $t>0$, the difference quotient $u_t(x)=(f(x)-T_{e^{-t}}f(x))/t$, where $T_\rho$ denotes Gaussian noise. By the definition of the Gaussian generator, $u_t$ converges to $g$ in Gaussian $L^2$ as $t\downarrow0$, and the quotients are themselves square-integrable for positive $t$ (`memLp_gaussianGeneratorQuotient`). Continuity of taking a Hermite coefficient under $L^2$ convergence (`tendsto_hermiteCoeff_of_eLpNorm_sub_tendsto`) therefore shows that the coefficients of $u_t$ converge to the coefficient of $g$. For each positive $t$, the quotient coefficient identity (`hermiteCoeff_gaussianGeneratorQuotient`) identifies it as $\bigl(1-e^{-t|\alpha|}\bigr)/t$ times the coefficient of $f$. The scalar factor tends to $|\alpha|$ as $t\downarrow0$ (`gaussianGeneratorMultiplier_tendsto`), so these same coefficients converge to $|\alpha|$ times the coefficient of $f$. Uniqueness of limits gives the claimed equality.

**Key facts.** `BooleanAnalysis.GaussianSpace.memLp_gaussianGeneratorQuotient`, `BooleanAnalysis.GaussianSpace.tendsto_hermiteCoeff_of_eLpNorm_sub_tendsto`, `BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_tendsto`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_gaussianGeneratorQuotient`.
