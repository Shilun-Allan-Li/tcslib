<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_singleton_factorization_of_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton factorization under a product law

**Claim.** If the conditional law of the special-bit pair is the product of the two conditional marginal laws, then each pair singleton has mass equal to the product of the corresponding marginal singleton masses.

**Proof.** Write $b=(b_X,b_Y)$. The assumed equality of measures lets us compute the pair law's mass at $\{(b_X,b_Y)\}$ using the product measure. This singleton is the rectangle $\{b_X\}\times\{b_Y\}$, and a product measure assigns that rectangle the product of the two marginal masses. Taking real masses preserves this product, yielding the stated equality.
