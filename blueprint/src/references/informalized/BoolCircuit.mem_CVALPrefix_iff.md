<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEval.lean :: BoolCircuit.mem_CVALPrefix_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Circuit Validation

**Claim.** A bit string belongs to the prefix circuit-value language exactly when the specified evaluator accepts it.

**Proof.** For the forward implication, unpack a witness to language membership: an input string $x$, a number $n$ no greater than its length, and a fan-in-two circuit $C$ that accepts the first $n$ bits, with the given string equal to the pair encoding of $C$’s code and $x$. The evaluator’s characterization on pair encodings (`BoolCircuit.CircuitEval.verdict_pairEncode`) applies with the prefix setting, since it permits $n\le |x|$ when exact length is not required. It therefore returns true. Conversely, if the evaluator returns true, decode the input into a code and string. If decoding fails, the evaluator cannot return true. If it succeeds, the decoded pair re-encodes to the original string (`Turing.eq_pairEncode_of_pairDecode`). Apply the evaluator characterization to this pair to obtain a circuit, a code match, the length bound, and acceptance on the specified prefix. The code match and re-encoding equality give the required language witness.

**Key facts.** `BoolCircuit.CircuitEval.verdict_pairEncode`, `Turing.eq_pairEncode_of_pairDecode`.
