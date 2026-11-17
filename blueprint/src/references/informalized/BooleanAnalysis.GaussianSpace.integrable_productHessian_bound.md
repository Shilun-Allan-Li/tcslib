<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductBounds.lean :: BooleanAnalysis.GaussianSpace.integrable_productHessian_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Gaussian quadratic bound

**Claim.** For a finite index set, the stated sum of centered coordinate squares, divided by $2v^2$ and increased by $1/v$, is integrable under the product Gaussian measure, including when $v=0$ with the specified division convention.

**Proof.** Each centered coordinate square is integrable under the product Gaussian measure by `integrable_centered_sq_gaussianCoordinate`. Adding the two such functions preserves integrability; multiplying by the fixed scalar $1/(2v^2)$ also preserves it. The remaining term $1/v$ is a constant function and hence integrable. Adding that constant gives the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_centered_sq_gaussianCoordinate`.
