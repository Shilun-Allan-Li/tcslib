<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Integration.lean :: BooleanAnalysis.GaussianSpace.integral_Iic_standardGaussianMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian integral over a half-line

**Claim.** For every function $f$ and real number $t$, its integral over $(-\infty,t]$ under the standard Gaussian measure equals the Lebesgue integral there of the Gaussian density times $f$.

**Proof.** Write the integral over the half-line as the integral of $f$ multiplied by the indicator of $(-\infty,t]$. The standard Gaussian measure has density $\varphi$ relative to Lebesgue measure, so the Gaussian integral becomes the Lebesgue integral of $\varphi f$ multiplied by the same indicator. This is precisely the Lebesgue integral over the half-line of $\varphi(x)f(x)$. The identity holds without integrability assumptions, as an equality of the corresponding integrals.
