<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.vertexValue_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex Values After Appending Gates

**Claim.** For any vertex $v<n+|gs|$, its Boolean value after applying $gs$ followed by $ext$ to the input assignment $x$ equals its value after applying $gs$ alone.

**Proof.** Processing the concatenated list $gs$ and $ext$ amounts to processing $ext$ starting from the values produced by $gs$ (`BoolCircuit.runWith_append`). A subsequent run preserves every entry whose index is within that starting list (`BoolCircuit.runWith_getD_of_lt`). Since the initial value list has length $n$ and each gate appends one value, the list after $gs$ has length $n+|gs|$. Thus $v$ is an existing entry, and its value is unchanged.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_getD_of_lt`.
