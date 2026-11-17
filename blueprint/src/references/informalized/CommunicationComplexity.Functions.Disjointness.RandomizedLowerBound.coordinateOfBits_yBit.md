<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_yBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering Bob’s bit

**Claim.** When Alice’s and Bob’s bits are not both true, extracting Bob’s bit from the coordinate formed from them returns Bob’s input bit.

**Proof.** Check the four possible Boolean pairs. If Bob’s bit is false, the constructed coordinate is either neither or left-only, whose Bob-bit is false. If Bob’s bit is true, the hypothesis forces Alice’s bit to be false, so the coordinate is right-only and its Bob-bit is true. Therefore the extracted bit equals Bob’s bit in every allowed case.
