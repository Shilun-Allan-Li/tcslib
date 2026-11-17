<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: BoolCircuit.DAGCircuit.one_le_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive circuit size

**Claim.** For a Boolean circuit with $n$ inputs, gates in topological order, and a valid output vertex, the size—defined as the number of inputs plus the number of gates—is at least $1$.

**Proof.** The output index is a natural number strictly below the circuit size. Hence the size cannot be zero, and so it is at least $1$.
