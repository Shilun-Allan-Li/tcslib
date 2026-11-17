<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.integral_Iic_id_mul_standardGaussianPDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncated Gaussian first moment

**Claim.** For every real $t$, the integral of $x\varphi(x)$ over $(-\infty,t]$ is $-\varphi(t)$.

**Proof.** Take the antiderivative $-\varphi(x)$: since $\varphi'(x)=-x\varphi(x)$, its derivative is $x\varphi(x)$. The density is continuous, the integrand is integrable on the half-line by integrability of the full first moment, and $\varphi(x)\to0$ as $x\to-\infty$. The fundamental theorem for integrals over lower half-lines therefore identifies the integral with the antiderivative's value at $t$ minus its limit at $-\infty$, giving $-\varphi(t)$. These derivative, continuity, integrability, and limit facts are supplied respectively by `hasDerivAt_standardGaussianPDF`, `continuous_standardGaussianPDF`, `integrable_id_mul_standardGaussianPDF`, and `tendsto_standardGaussianPDF_atBot`.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianPDF`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianPDF`, `BooleanAnalysis.ThresholdFunctions.integrable_id_mul_standardGaussianPDF`, `BooleanAnalysis.ThresholdFunctions.tendsto_standardGaussianPDF_atBot`.
