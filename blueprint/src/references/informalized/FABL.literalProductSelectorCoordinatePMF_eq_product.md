<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.literalProductSelectorCoordinatePMF_eq_product -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise Product Law

**Claim.** The law of the vector of output value pairs is the product, over coordinates, of the corresponding one-coordinate law.

**Proof.** Condition first on the sampled first vector. For each fixed first vector, the remaining sampling independently chooses the second vector and the selector pairs across coordinates. The factorization after fixing the first vector (`literalSelector_after_plus`) rewrites this conditional law as the product of the one-coordinate laws, each conditioned on that coordinate of the fixed vector. Averaging over the first vector then uses the product-distribution bind identity (`productProbabilityPMF_bind_coordinates`): binding a product law through coordinatewise conditional laws gives the product of the one-coordinate marginal mixtures. Each marginal mixture is exactly the specified one-coordinate selector law, yielding the claimed equality.

**Key facts.** `FABL.literalSelector_after_plus`, `FABL.productProbabilityPMF_bind_coordinates`.
