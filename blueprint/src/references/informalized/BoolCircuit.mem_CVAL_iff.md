<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEval.lean :: BoolCircuit.mem_CVAL_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-Value Validation

**Claim.** A bit string belongs to the circuit-value language exactly when the specified evaluator accepts it.

**Proof.** For the forward implication, unpack a witness consisting of an input string $x$, a circuit $C$ with exactly $|x|$ input variables, its fan-in-two condition, and acceptance on $x$. The evaluator characterization for pair encodings (`BoolCircuit.CircuitEval.verdict_pairEncode`) applies with the exact-length option; identify the evaluator’s defaulted input values with the entries of $x$, so it accepts the encoded pair. Conversely, decode a string on which the evaluator accepts. Decoding must succeed; the decoded code and input re-encode to the original string (`Turing.eq_pairEncode_of_pairDecode`). The evaluator characterization supplies a fan-in-two circuit with that code, an input-length bound, exact equality of the circuit’s variable count and input length, and acceptance on the input. The exact equality gives a circuit of the required input size; again identify the defaulted-input evaluation with evaluation on the list itself. Together with the re-encoding equality these data form a witness for membership in the circuit-value language.

**Key facts.** `BoolCircuit.CircuitEval.verdict_pairEncode`, `Turing.eq_pairEncode_of_pairDecode`.
