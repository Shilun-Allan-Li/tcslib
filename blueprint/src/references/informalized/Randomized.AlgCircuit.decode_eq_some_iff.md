<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.decode_eq_some_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of circuit decoding

**Claim.** For every Boolean list $x$ and every finite-input arithmetic circuit $C$, decoding $x$ returns $C$ exactly if and only if $x$ is the Boolean-list encoding of $C$.

**Proof.** If decoding $x$ returns $C$, the recovery property says that encoding $C$ gives back $x$ (`encode_of_decode`). Conversely, if encoding $C$ is $x$, decode both sides: decoding an encoded circuit returns that circuit (`decode_encode`), so decoding $x$ returns $C$.

**Key facts.** `Randomized.AlgCircuit.encode_of_decode`, `Randomized.AlgCircuit.decode_encode`.
