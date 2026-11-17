<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_eq_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF Integral Formula

**Claim.** The standard Gaussian distribution function at $t$ equals the integral of the standard Gaussian density over $(-\infty,t]$.

**Proof.** Unfold the definitions of the standard Gaussian measure, density, and CDF. The CDF is the measure of $(-\infty,t]$; for the Gaussian measure, this measure is the integral of its density over that interval. The measure is already a nonnegative real quantity, so converting its real-valued measure representation gives exactly the asserted integral.
