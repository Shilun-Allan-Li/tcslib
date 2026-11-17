<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_xBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering Alice’s bit

**Claim.** When the two input bits are not both true, extracting Alice’s bit from the coordinate formed from them returns the first input bit.

**Proof.** Check the four possible pairs of Boolean values. If the first bit is false, the constructed coordinate is either neither or right-only, and Alice’s bit is false in both cases. If the first bit is true, the hypothesis forces the second bit to be false, so the coordinate is left-only and Alice’s bit is true. Thus the extracted bit equals the first input bit in every allowed case.
