<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_yBit_of_mem_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of Bob's bit

**Claim.** For a sample in the disjointness event, the Bob-bit of the generated disjoint coordinate at each position agrees with Bob's bit at that position.

**Proof.** By the characterization of disjointness, the special bits cannot both be true (`disjoint_X_Y_iff`). The coordinate encoding therefore recovers Bob's bit from the special-bit pair (`coordinateOfBits_yBit`). At the distinguished coordinate, the generated label is that encoding. At every other coordinate, both the generated label and Bob's bit are read from the stored coordinate label, giving the equality there as well.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjoint_X_Y_iff`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_yBit`.
