<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.encodeChildren_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding the Empty Child List

**Claim.** For any natural number $n$, the encoding of the empty list of circuit trees on $n$ variables is $[0]$.

**Proof.** By definition, encoding the children first concatenates the encodings contributed by each child and then appends the terminator $[0]$. The empty list contributes no child bits, so only the terminator remains.
