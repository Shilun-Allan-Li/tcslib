<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCoordinateVector_xBit_of_mem_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of Alice's bit

**Claim.** For a sample in the disjointness event, the Alice-bit of the generated disjoint coordinate at each position agrees with Alice's bit at that position.

**Proof.** Disjointness of the input sets is equivalent to saying that the two special bits are not both true (`disjoint_X_Y_iff`). Hence the special bits form a pair to which the coordinate encoding recovers Alice's bit (`coordinateOfBits_xBit`). If the position is the distinguished coordinate $T$, the generated coordinate is precisely this encoding, so the claimed equality follows. At any other position, the generated coordinate is the stored label, and both sides read Alice's bit from that same label.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjoint_X_Y_iff`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_xBit`.
