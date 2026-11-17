<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorFuel_fanin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin bound for XOR reduction

**Claim.** For a list of at most $k$ pairs, the maximum fan-in of the pair returned by the fuel-bounded XOR reduction is at most the larger of $2$ and the pair fan-in of the original list.

**Proof.** Induct on the fuel, distinguishing empty, singleton, and longer lists. For the empty list, the output consists of constant nodes, whose fan-in is zero. For a singleton, the pair is returned unchanged, so its maximum fan-in is bounded by the pair fan-in of the list.

For a list with at least two pairs, one pairing round combines consecutive pairs using an XOR step. The length formula ensures the resulting list fits within the reduced fuel, so the induction hypothesis applies to it. The pair fan-in after this round is at most the larger of two and the original pair fan-in (`pairFanin_xorPairUp`). Combining that bound with the induction hypothesis yields the claimed maximum fan-in bound for the returned pair.

**Key facts.** `BoolCircuit.length_xorPairUp`, `BoolCircuit.pairFanin_xorPairUp`.
