<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_gaussianProjection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian law of a unit projection

**Claim.** If the coefficients have squared sum one, their linear combination of independent standard Gaussian coordinates has the standard Gaussian law.

**Proof.** Under the product standard Gaussian measure, the coordinate evaluation maps are measurable, each has the standard Gaussian law, and they are independent. The sum-of-scaled-independent-Gaussians formula (`sum_scaled_iid_gaussian_map`) therefore says that the weighted sum has centered Gaussian law with variance equal to the sum of the squared coefficients. By hypothesis that sum is one, so this law is standard Gaussian. The linear combination is measurable, and its pushforward law being the original standard Gaussian measure gives the claimed measure preservation.

**Key facts.** `sum_scaled_iid_gaussian_map`.
