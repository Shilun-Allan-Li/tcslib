<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Polynomial.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussian_affine_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Gaussian affine monomials

**Claim.** For a finite set of coordinates $S$, the function $y\mapsto\prod_{i\in S}(a_i+s y_i)$ is integrable under the product standard Gaussian measure.

**Proof.** For each coordinate $i$, consider the factor that equals $a_i+s y_i$ when $i\in S$ and equals $1$ otherwise. If $i\in S$, this factor is integrable because constants and scalar multiples of the standard Gaussian coordinate are integrable, and sums of integrable functions remain integrable. If $i\notin S$, it is the constant function $1$, hence integrable. Independence of the coordinates, expressed by the product measure, then implies that the finite product of these one-coordinate factors is integrable. That product is exactly the stated monomial.
