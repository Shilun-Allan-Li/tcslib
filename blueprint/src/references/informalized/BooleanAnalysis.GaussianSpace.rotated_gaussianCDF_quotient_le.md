<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.rotated_gaussianCDF_quotient_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF rotation quotient bound

**Claim.** For real t and y and 0 < θ < 1, the absolute change in the standard Gaussian CDF under the stated rotation and rescaling, divided by θ, is at most 2φ(0)(|t|+|y|).

**Proof.** On this range of θ, the cosine bound for angles below one gives cos θ ≥ 1/2, and hence cos θ is positive. The same trigonometric bound implies |1−cos θ| ≤ θ, while |sin θ| ≤ θ. Writing the change in the CDF's arguments as a single fraction, its numerator is t(1−cos θ)−sin θ·y. The triangle inequality and these trigonometric estimates bound the absolute difference of the arguments by 2θ(|t|+|y|), using cos θ ≥ 1/2 to control division by cos θ. The Gaussian CDF is Lipschitz with constant φ(0), by `abs_standardGaussianCDF_sub_le`. Applying that estimate and dividing by positive θ proves the result; positivity of the Gaussian density (`standardGaussianPDF_pos`) justifies preserving the inequality when multiplying.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_standardGaussianCDF_sub_le`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
