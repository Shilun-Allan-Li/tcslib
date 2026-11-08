<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.evalLiteral_toCktLiteral_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Evaluation and Encoding

**Claim.** Under an assignment b1 consistent with the Boolean input assignment , the encoded circuit literal is true exactly when the original literal evaluates to true.

**Proof.** Split according to the literal's sign and the value of its indexed input. In each of the four cases, the consistency hypothesis identifies whether that input is true under  with whether b1 makes the corresponding input variable true. The definitions of literal evaluation and literal encoding then give the same truth value on both sides, including when the literal is negated.
