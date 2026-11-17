<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDensity.lean :: BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Second Coordinate Moment

**Claim.** For independent Gaussian coordinates with means $c_j$ and common variance $v$, the expected squared deviation of coordinate $i$ from its mean is $v$.

**Proof.** Under the product measure, coordinate evaluation at $i$ has distribution $N(c_i,v)$; this follows from the measure-preserving coordinate projection. Therefore the integral of $(z_i-c_i)^2$ over the product equals its integral under that one-dimensional Gaussian. The centered second-moment identity for a Gaussian (`integral_centered_sq_gaussianReal`) evaluates the latter integral as $v$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianReal`.
