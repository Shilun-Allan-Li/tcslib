<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_iIndepFun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of the coordinates

**Claim.** Under the uniform law on coordinate vectors, the coordinate maps are mutually independent.

**Proof.** By the product-measure identity (`uniformDisjointCoordinateVector_eq_pi`), the vector law is the product of the uniform single-coordinate laws. Under a product measure, the coordinate projections are mutually independent; applying that fact gives the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_eq_pi`.
