<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.parseGates_encodeGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing an Encoded Gate List

**Claim.** If a finite gate list has length at most the parsing budget, parsing its Boolean encoding with that budget returns exactly the original list.

**Proof.** Proceed by induction on the gate list, allowing the budget to vary. For the empty list, its encoding is the terminator, which the parser sends to the empty list. For a nonempty list, the length bound ensures the budget is positive; write it as one more than a smaller budget. The gate parser recovers the first gate and leaves the encoding of the remaining list, by the gate parsing theorem (`Randomized.AlgGate.parse_encode`). The induction hypothesis applies to the tail because its length is at most the smaller budget. Thus parsing reconstructs the head followed by the original tail.

**Key facts.** `Randomized.AlgGate.parse_encode`.
