<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.prod_measureReal_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton mass of a product measure

**Claim.** For measurable spaces $\alpha$ and $\beta$, a measure $\mu_1$ on $\alpha$, and a sigma-finite measure $\mu_2$ on $\beta$, the product measure of a singleton pair is the product of the two singleton masses.

**Proof.** The singleton containing $(x,y)$ is the measurable rectangle $\{x\}\times\{y\}$. The product-measure formula on rectangles therefore gives its mass as $\mu_1(\{x\})\mu_2(\{y\})$. Passing to real-valued measures preserves this product, giving the asserted identity.
