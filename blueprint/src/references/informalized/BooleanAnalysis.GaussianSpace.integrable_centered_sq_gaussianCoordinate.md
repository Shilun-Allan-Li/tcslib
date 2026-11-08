<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDensity.lean :: BooleanAnalysis.GaussianSpace.integrable_centered_sq_gaussianCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Gaussian Coordinate Integrability

**Claim.** For a finite index set, a Gaussian product measure with coordinate means $c_j$ and variance parameter $v\ge 0$ integrates the centered square $(z_i-c_i)^2$ for each coordinate $i$.

**Proof.** The $i$th coordinate under the product measure has law $\operatorname{gaussianReal}(c_i,v)$, because coordinate evaluation preserves measure from that Gaussian measure to the product. Under this one-dimensional Gaussian law, the identity function belongs to $L^2$; subtracting the constant $c_i$ preserves membership in $L^2$. Its square is therefore integrable. Composing this integrable function with the measure-preserving coordinate evaluation gives the claimed integrability on the product space.
