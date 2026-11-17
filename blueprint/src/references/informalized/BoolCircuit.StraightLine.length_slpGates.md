<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.length_slpGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Gate List

**Claim.** The gate list formed by the $n$ input-negation gates followed by one gate for each straight-line statement has length $n+|ss|$.

**Proof.** The input-negation list has length $n$, since it contains one gate for each index in the range of length $n$. Mapping the statements to gates preserves their length, so the second list has length $|ss|$. The length of their concatenation is the sum of these lengths, namely $n+|ss|$.
