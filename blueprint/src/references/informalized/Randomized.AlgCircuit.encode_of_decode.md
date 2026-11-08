<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.encode_of_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of an encoded circuit

**Claim.** For a natural number of inputs and an algebraic circuit on those inputs, if decoding a Boolean list returns that circuit, then encoding the circuit recovers the list.

**Proof.** Unfold the definition of decoding in the assumed equality. The cases where the initial natural-number decoding or the subsequent gate parsing fails cannot produce a successful result. In the remaining case, decoding returns the parsed circuit only when the final encoding check holds. Equality with the specified circuit therefore identifies that parsed circuit with the given one, and the encoding check yields that encoding the given circuit recovers the original list.
