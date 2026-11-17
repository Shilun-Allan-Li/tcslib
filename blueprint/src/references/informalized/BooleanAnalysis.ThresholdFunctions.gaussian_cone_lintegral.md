<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianPolar.lean :: BooleanAnalysis.ThresholdFunctions.gaussian_cone_lintegral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian mass of a cone

**Claim.** Under the stated angular membership condition, the planar standard Gaussian mass of $A$ equals $(2\pi)^{-1}$ times the Lebesgue measure of $\Theta\cap(-\pi,\pi)$.

**Proof.** Use polar coordinates with radius $r>0$ and angle $\theta\in(-\pi,\pi)$. The cone condition says that in these coordinates the indicator of $A$ depends only on whether $\theta\in\Theta$. The polar change of variables contributes the radial Jacobian $r$, so the density times the Jacobian factors as $(2\pi)^{-1}\exp(-r^2/2)r$ times the angular indicator. Thus the integral over $A$ factors into the angular measure of $\Theta\cap(-\pi,\pi)$, multiplied by $(2\pi)^{-1}$ and the radial integral $\int_0^\infty r\exp(-r^2/2)\,dr$. This radial integral equals $1$ (`lintegral_radial`), giving the asserted formula. The origin is excluded from the polar coordinate domain and has measure zero, so it does not affect the integral.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.lintegral_radial`.
