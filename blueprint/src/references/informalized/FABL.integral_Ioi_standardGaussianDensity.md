<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.integral_Ioi_standardGaussianDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian Upper Tail Density Integral

**Claim.** For every real $t$, the integral of the standard Gaussian density over $x>t$ equals the standard Gaussian upper tail probability at $t$.

**Proof.** The standard Gaussian upper tail is the real measure of the interval $(t,\infty)$ (`standardGaussianUpperTail_eq_measureReal_Ioi`). Expressing that measure through the Gaussian density identifies it with the real-valued integral of the density over the same interval. The density is nonnegative, so converting the nonnegative integral from its extended-real measure expression to a real integral gives the claimed equality.

**Key facts.** `FABL.standardGaussianUpperTail_eq_measureReal_Ioi`.
