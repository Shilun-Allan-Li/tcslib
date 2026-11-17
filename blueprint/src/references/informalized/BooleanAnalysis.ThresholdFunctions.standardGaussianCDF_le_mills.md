<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_le_mills -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Lower-Tail Bound

**Claim.** For $t<0$, the standard Gaussian CDF satisfies $\Phi(t)\le \phi(t)/(-t)$, where $\phi$ is the standard Gaussian density.

**Proof.** For every $x\le t<0$, we have $x/t\ge1$. Since the Gaussian density is positive, this gives $\phi(x)\le (x/t)\phi(x)=t^{-1}x\phi(x)$. Integrating over $(-\infty,t]$ bounds the CDF by $t^{-1}$ times the integral of $x\phi(x)$ over that interval. The Gaussian density’s first-moment integral on this interval is $-\phi(t)$ (the identity supplied by `integral_Iic_id_mul_standardGaussianPDF`), so the bound becomes $-t^{-1}\phi(t)=\phi(t)/(-t)$. The CDF is represented by the density integral (`standardGaussianCDF_eq_integral`). Positivity of the density (`standardGaussianPDF_pos`) justifies the pointwise comparison, and integrability of $x\phi(x)$ (`integrable_id_mul_standardGaussianPDF`) ensures the comparison applies to the integrals.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.integrable_id_mul_standardGaussianPDF`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`, `BooleanAnalysis.ThresholdFunctions.integral_Iic_id_mul_standardGaussianPDF`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_eq_integral`.
