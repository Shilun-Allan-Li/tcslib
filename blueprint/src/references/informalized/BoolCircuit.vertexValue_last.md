<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.vertexValue_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Last Vertex

**Claim.** After applying $gs$ and then $g$ to the input assignment $x$, the value at vertex $n+|gs|$ is the evaluation of $g$ on the values obtained after applying $gs$ to $x$.

**Proof.** For a run with a final gate appended, the entry at index $|init|+|gs|$ is the output of that gate evaluated on the list produced by the preceding run (`BoolCircuit.runWith_getD_last`). The initial list of input values has length $n$, and the gate output here is its Boolean evaluation on the current list. These identifications give the stated equality.

**Key facts.** `BoolCircuit.runWith_getD_last`.
