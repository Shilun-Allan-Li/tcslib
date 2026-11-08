<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgePrimUnnumber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Sentinel Decoding

**Claim.** The function sending a natural number to the Boolean string obtained by reversing its binary expansion, deleting the final bit, and reversing the remaining string is primitive recursive.

**Proof.** The binary expansion map is primitive recursive by `Turing.codePrimBits`. The list operations of reversal and taking the tail are also primitive recursive. Composing these maps in the order used in the definition—first reverse the binary expansion, then delete its first entry by taking the tail, and finally reverse the resulting list—shows that sentinel decoding is primitive recursive.

**Key facts.** `Turing.codePrimBits`.
