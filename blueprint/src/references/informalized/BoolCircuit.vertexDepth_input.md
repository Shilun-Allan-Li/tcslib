<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.vertexDepth_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of an Input Vertex

**Claim.** If $i<n$, then after applying any gate list $gs$ to $n$ initial input vertices, vertex $i$ has depth zero.

**Proof.** The list of initial depths consists of $n$ zeros, so its entry at index $i<n$ is zero. Processing gates preserves every entry already present in the initial list, by `BoolCircuit.runWith_getD_of_lt`. Thus the depth read at index $i$ after the run is that same initial zero.

**Key facts.** `BoolCircuit.runWith_getD_of_lt`.
