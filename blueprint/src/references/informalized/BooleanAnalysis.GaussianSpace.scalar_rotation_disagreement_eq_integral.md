<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.scalar_rotation_disagreement_eq_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Disagreement as a Gaussian Integral

**Claim.** When $\cos\theta>0$, the probability that the two scalar Gaussian threshold indicators disagree equals the integral of the absolute difference of the two Gaussian CDF values stated in the claim.

**Proof.** First integrate the disagreement event by conditioning on the second coordinate $y$, using the product-measure section formula; measurability of the event makes this integration valid (measurableSet_scalar_rotation_disagreement). For fixed $y$, the rotated inequality $\cos\theta\,x+\sin\theta\,y\le t$ is equivalent, because $\cos\theta>0$, to $x\le (t-\sin\theta\,y)/\cos\theta$. Hence the section in the $x$ coordinate is the symmetric difference of the two lower rays with endpoints $t$ and $(t-\sin\theta\,y)/\cos\theta$. The standard Gaussian measure of a symmetric difference of such rays is the absolute difference of their CDF values (standardGaussianMeasure_symmDiff_Iic). Integrating this section measure over $y$ gives the desired formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurableSet_scalar_rotation_disagreement`, `BooleanAnalysis.GaussianSpace.standardGaussianMeasure_symmDiff_Iic`.
