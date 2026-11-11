<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_gaussianGeneratorQuotient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficient of the Noise Quotient

**Claim.** For positive $t$, the Hermite coefficient of the Gaussian noise difference quotient of $f$ at $\alpha$ is the coefficient of $f$ multiplied by $\bigl(1-e^{-t|\alpha|}\bigr)/t$.

**Proof.** Since $t>0$, the correlation parameter $e^{-t}$ lies in $[-1,1]$ (`exp_neg_mem_correlationInterval`). Gaussian noise with such a parameter preserves square-integrability (`gaussianNoise_memLp`), so both terms in the difference quotient have well-defined coefficients. Linearity of the Hermite coefficient in scalar multiplication and subtraction (`hermiteCoeff_const_mul`, `hermiteCoeff_sub`) reduces the coefficient to $t^{-1}$ times the coefficient of $f$ minus $t^{-1}$ times the coefficient of its Gaussian smoothing. The noise action on Hermite coefficients multiplies the coefficient at $\alpha$ by $e^{-t|\alpha|}$ (`hermiteCoeff_gaussianNoise`). Combining these expressions yields $t^{-1}(1-e^{-t|\alpha|})$ times the coefficient of $f$, which is exactly the stated multiplier.

**Key facts.** `BooleanAnalysis.GaussianSpace.exp_neg_mem_correlationInterval`, `BooleanAnalysis.GaussianSpace.gaussianNoise_memLp`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_const_mul`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_sub`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_gaussianNoise`.
