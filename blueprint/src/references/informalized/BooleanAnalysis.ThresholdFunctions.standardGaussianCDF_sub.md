<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Distribution Increments

**Claim.** For all real numbers $a$ and $b$, $\Phi(b)-\Phi(a)=\int_a^b\varphi(x)\,dx$, where the interval integral is signed.

**Proof.** Express each CDF value as the integral of the standard Gaussian density over the corresponding lower half-line, using `standardGaussianCDF_eq_integral`. The difference of these two half-line integrals is the signed interval integral from $a$ to $b$: the additivity formula for interval integrals gives the result. The Gaussian density is integrable on each such half-line, as required for that formula.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_eq_integral`.
