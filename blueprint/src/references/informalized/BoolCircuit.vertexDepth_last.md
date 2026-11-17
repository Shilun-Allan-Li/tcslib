<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.vertexDepth_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of the Last Vertex

**Claim.** After applying $gs$ and then a gate $g$ to $n$ initial vertices, the depth of the newly appended vertex at index $n+|gs|$ is the depth of $g$ evaluated from the depths after applying $gs$.

**Proof.** The last-entry formula for a run followed by one gate says that the entry at index $|init|+|gs|$ is the value of the final gate applied to the list obtained after processing $gs$ (`BoolCircuit.runWith_getD_last`). Here the initial list has length $n$, and the gate's output is defined to be its depth computed from the current list of depths. Substituting these definitions gives the asserted equality.

**Key facts.** `BoolCircuit.runWith_getD_last`.
