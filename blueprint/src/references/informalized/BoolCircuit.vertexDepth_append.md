<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.vertexDepth_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex Depth Under Appending Gates

**Claim.** For any vertex index $v<n+|gs|$, processing the gate list $gs$ followed by $ext$ gives vertex $v$ the same depth as processing $gs$ alone, starting from $n$ input vertices of depth zero.

**Proof.** By the decomposition of a run over concatenated gate lists, processing $gs$ followed by $ext$ is the same as first processing $gs$ and then processing $ext$ from the resulting list of depths (`BoolCircuit.runWith_append`). The list after processing $gs$ has its first $n+|gs|$ entries unchanged when more gates are processed: `BoolCircuit.runWith_getD_of_lt` states that a run preserves every entry whose index is within the initial list. The hypothesis $v<n+|gs|$ places $v$ among those entries, so the two reported depths agree.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_getD_of_lt`.
