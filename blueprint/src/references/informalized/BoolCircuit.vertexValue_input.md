<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.vertexValue_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of an Input Vertex

**Claim.** For an input assignment $x$ and input index $i$, the value at vertex $i$ after applying any gate list $gs$ is $x(i)$.

**Proof.** The initial list of Boolean values is formed from $x$, and its entry at index $i$ is $x(i)$. Since $i$ is an input index, it lies within this initial list. Processing the gates preserves that entry by `BoolCircuit.runWith_getD_of_lt`, so the value at vertex $i$ remains $x(i)$.

**Key facts.** `BoolCircuit.runWith_getD_of_lt`.
