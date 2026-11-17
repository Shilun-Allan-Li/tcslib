<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.length_negGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Negation-Gate List

**Claim.** The list containing one unary negation gate for each index from $0$ through $n-1$ has length $n$.

**Proof.** The list is obtained by mapping a function over the range from $0$ to $n-1$. Mapping preserves list length, and that range has length $n$.
