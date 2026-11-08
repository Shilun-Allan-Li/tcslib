<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.rotated_gaussianCDF_quotient_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Limit of the Gaussian CDF rotation quotient

**Claim.** For fixed real t and y, as θ tends to zero from above, the absolute Gaussian CDF rotation quotient converges to φ(t)|y|.

**Proof.** The derivative formula `hasDerivAt_rotated_gaussianCDF` gives the derivative at zero of the difference between the rotated CDF and its value at t: it is −φ(t)y. The theorem relating a derivative to the limit of right-hand difference quotients therefore gives convergence of that signed quotient to −φ(t)y. Taking absolute values gives the limit φ(t)|y|, since the Gaussian density is positive (`standardGaussianPDF_pos`). On the positive side of zero, the quotient with denominator θ is exactly the absolute value of that difference quotient. Thus the desired one-sided limit follows.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_rotated_gaussianCDF`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
