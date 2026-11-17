<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.mem_PITLang_iff_pitToZerop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction from PIT to Zero Testing

**Claim.** A string is a valid polynomial identity testing instance exactly when the string produced by the PIT-to-zero-testing construction encodes a well-formed circuit computing the zero polynomial.

**Proof.** 1. Rewrite PIT membership using `Randomized.mem_PITLang_iff`, and zero-testing membership using `Randomized.mem_ZEROP_iff`. Split according to whether the input passes the construction's validity check `pitPairOk`.

2. If it passes, `Randomized.pitPairOk_iff` supplies a common variable count and two decoded, well-formed circuits. The construction identity `Randomized.PIT.subW_eq` says the output is exactly the encoding of their difference circuit. The circuit encoding theorem `Randomized.AlgCircuit.decode_encode` decodes that output as the difference circuit. For the forward implication, any zero-testing witness must be this same decoded circuit; its well-formedness follows from `Randomized.AlgCircuit.WellFormed.subCircuit`, and its zero polynomial implies equality of the original polynomials by `Randomized.AlgCircuit.toMvPolynomial_eq_iff_subCircuit`. For the reverse implication, take the difference circuit itself as the zero-testing witness and use the other direction of that same polynomial equivalence.

3. If the validity check fails, PIT membership is impossible by the reverse implication of `Randomized.pitPairOk_iff`. The constructed output is the empty string. Were that string in the zero-testing language, `Randomized.mem_ZEROP_iff` would provide a decoded circuit encoding it. But every circuit encoding is longer than its variable count plus circuit size (`Randomized.AlgCircuit.lt_length_encode`), so it cannot encode the empty string. Thus neither side holds in this case.

**Key facts.** `Randomized.mem_PITLang_iff`, `Randomized.mem_ZEROP_iff`, `Randomized.pitPairOk_iff`, `Randomized.PIT.subW_eq`, `Randomized.AlgCircuit.decode_encode`, `Randomized.AlgCircuit.WellFormed.subCircuit`, `Randomized.AlgCircuit.toMvPolynomial_eq_iff_subCircuit`, `Randomized.AlgCircuit.lt_length_encode`.
