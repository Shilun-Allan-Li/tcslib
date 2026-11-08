<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.hasDerivAt_gaussianIsoperimetricInterior -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian interior profile

**Claim.** At every $\alpha\in(0,1)$, the Gaussian isoperimetric interior profile is differentiable, with derivative the standard Gaussian upper quantile at $\alpha$.

**Proof.** Differentiate the standard Gaussian upper quantile as a function of $\alpha$; its derivative is the negative reciprocal of the Gaussian isoperimetric profile (`FABL.hasDerivAt_standardGaussianUpperQuantileReal`). The Gaussian density, composed with this quantile, therefore has derivative given by the density derivative (`FABL.hasDerivAt_standardGaussianDensity`) times that quantile derivative. The density derivative at the quantile is minus the quantile times the density, so the product simplifies to the quantile. The density is nonzero, since the Gaussian density is positive; this justifies the cancellation. On the interior, the real-valued profile agrees with the density evaluated at the quantile (`FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo`), and the real-valued quantile agrees with the interval-valued quantile (`FABL.standardGaussianUpperQuantileReal_eq`). These identifications give the asserted derivative of the interior profile.

**Key facts.** `FABL.hasDerivAt_standardGaussianUpperQuantileReal`, `FABL.hasDerivAt_standardGaussianDensity`, `FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo`, `FABL.standardGaussianUpperQuantileReal_eq`.
