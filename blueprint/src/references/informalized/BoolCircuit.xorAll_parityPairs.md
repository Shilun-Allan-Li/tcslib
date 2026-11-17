<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorAll_parityPairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Pairs Evaluate to Input Parity

**Claim.** The accumulated exclusive-or over the parity-pair list evaluates to the exclusive-or of the input values over all variable indices.

**Proof.** The parity-pair list is formed by mapping each index in the finite range to a pair whose first circuit is the positive literal at that index. Induct on the finite-range list. The empty list gives false on both sides. For a leading index followed by a tail, the accumulation splits into the xor of the leading pair's first circuit value and the tail accumulation (`BoolCircuit.xorAll_cons`). The leading positive literal evaluates to the input value at that index. Applying the induction hypothesis to the tail yields exactly the corresponding fold of input values.

**Key facts.** `BoolCircuit.xorAll_cons`.
