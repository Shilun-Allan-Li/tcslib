<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product form of the uniform vector law

**Claim.** The uniform law on coordinate vectors equals the product of the uniform laws on individual disjoint coordinates.

**Proof.** It suffices to compare the real masses of singleton vectors. A particular vector has mass $1/3^n$ under the uniform vector law (`uniformDisjointCoordinateVector_singleton`). Under the product law, its singleton mass is the product of the coordinate singleton masses, each $1/3$ (`uniformDisjointCoordinate_singleton`), hence $(1/3)^n=1/3^n$. Since the spaces are finite, equality of all singleton masses gives equality of the measures.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinate_singleton`.
