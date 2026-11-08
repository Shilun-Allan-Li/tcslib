<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.integral_abs_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Absolute Gaussian Moment

**Claim.** The standard Gaussian measure on $\mathbb R$ has absolute first moment $2\varphi(0)$.

**Proof.** The standard Gaussian density is even, so the integral of $y\varphi(y)$ over the whole line is zero; this is also the mean-zero Gaussian identity used in the proof. Pointwise, $|y|=y-2y\,1_{(-\infty,0]}(y)$. Integrating this decomposition leaves minus twice the integral of $y\varphi(y)$ over $(-\infty,0]$. The Gaussian density tail identity (`integral_Iic_id_mul_standardGaussianPDF`) evaluates that half-line integral as $-\varphi(0)$. The result is $2\varphi(0)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.integral_Iic_id_mul_standardGaussianPDF`.
