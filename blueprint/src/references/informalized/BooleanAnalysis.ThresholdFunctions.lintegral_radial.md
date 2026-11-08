<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianPolar.lean :: BooleanAnalysis.ThresholdFunctions.lintegral_radial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radial Gaussian normalization

**Claim.** The nonnegative extended integral of $r e^{-r^2/2}$ over $r>0$ equals $1$.

**Proof.** First, the function $r\mapsto r e^{-r^2/2}$ is integrable on the positive half-line, by the standard integrability result for a polynomial times a decaying Gaussian exponential. Its ordinary integral there equals $1$: the complex Gaussian integral identity for $x e^{-b x^2}$, specialized to $b=1/2$, gives this value, and the real and complex integrals agree for a real-valued integrable function. On the positive half-line the integrand is nonnegative. Therefore its integral as an extended nonnegative function is equal to its ordinary integral, so the requested lintegral is $1$.
