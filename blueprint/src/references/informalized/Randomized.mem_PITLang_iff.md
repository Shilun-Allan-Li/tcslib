<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPPIT.lean :: Randomized.mem_PITLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the PIT Language

**Claim.** A string belongs to the polynomial identity testing language exactly when its two decoded components are encodings of well-formed circuits on the same number of variables whose computed polynomials are equal.

**Proof.** For the forward direction, unpack membership: the string is the pair encoding of two circuit encodings, the circuits are well formed, and their polynomials agree. The circuit decoding theorem `Randomized.AlgCircuit.decode_encode` recovers each circuit from its encoding, so these circuits witness the stated decoded characterization. For the reverse direction, let the two decoded components yield well-formed circuits on the same variable set with equal polynomials. The inverse property `Randomized.AlgCircuit.encode_of_decode` identifies each circuit encoding with its decoded component. The pair-decoding identity `Randomized.eq_pairEncode_of_decode` then reconstructs the original string as the pair encoding of those components. Thus the circuits and their polynomial equality witness membership in the PIT language.

**Key facts.** `Randomized.AlgCircuit.decode_encode`, `Randomized.AlgCircuit.encode_of_decode`, `Randomized.eq_pairEncode_of_decode`.
