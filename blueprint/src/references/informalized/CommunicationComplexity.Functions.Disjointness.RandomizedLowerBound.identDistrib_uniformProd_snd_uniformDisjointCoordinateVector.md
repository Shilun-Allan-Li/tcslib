<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_uniformProd_snd_uniformDisjointCoordinateVector -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second marginal of a product law

**Claim.** Under the product of the uniform law on special coordinates and the uniform law on disjoint-coordinate vectors, the second component has the uniform disjoint-coordinate-vector law.

**Proof.** The pushforward of a product measure under projection onto its second factor is that second-factor measure. Applying this product-measure marginal identity shows that projection onto the vector component has exactly the uniform disjoint-coordinate-vector law. The identity map leaves that law unchanged, so the two random variables in the statement are identically distributed.
