<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductBounds.lean :: BooleanAnalysis.GaussianSpace.integral_productHessian_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Quadratic Integral

**Claim.** For a finite index set and coordinates drawn independently from Gaussians with means given by $c$ and variance parameter $v>0$, the integral of the stated quadratic expression is $2/v$.

**Proof.** Each centered coordinate square is integrable and has integral $v$ under the product Gaussian measure (integrability and the second-moment identity are supplied by `integrable_centered_sq_gaussianCoordinate` and `integral_centered_sq_gaussianCoordinate`). Thus the sum of the two square terms is integrable, as is the constant term. By linearity of integration, the integral of the quadratic part is $(v+v)/(2v^2)=1/v$, while the integral of the constant $1/v$ is $1/v$, since the product Gaussian measure has total mass one. Adding these contributions gives $2/v$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_centered_sq_gaussianCoordinate`, `BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianCoordinate`.
