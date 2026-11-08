<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.integral_comp_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate marginal preserves integrals

**Claim.** Integrating a function of one coordinate over the finite product probability space gives the same value as integrating the function over one copy of the space.

**Proof.** Let $\nu$ be the product measure on the indexed copies of $\Omega$. The coordinate evaluation map at $i$ sends this product measure to the original measure: it is measure preserving, as follows from the product-measure marginal theorem. The integral change-of-variables formula for this map identifies the integral of $f(\omega_i)$ under $\nu$ with the integral of $f$ under the image measure. Substituting that the image measure is the original measure gives the equality.
