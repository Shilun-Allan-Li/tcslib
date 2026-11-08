<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.searchState_struct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structure of the search state

**Claim.** After $j$ stages, the search state has an acyclic gate list, exactly $j$ valid output vertices, includes vertex $n$, and every gate has distinct arguments, unary negations, and at most two arguments.

**Proof.** Proceed by induction on $j$. At stage zero the state consists of a single constant-true gate and no outputs. The gate is acyclic, the output list has length zero, vertex $n$ is present among the circuit vertices, and the constant gate satisfies the stated argument conditions. For the successor step, assume these properties for a state $s$. The new stage embeds the next circuit using as sources the original input vertices, the old output vertices, and vertex $n$. Each is an existing vertex: this follows from the induction hypotheses that old outputs are valid and that vertex $n$ is present. The source list has length $n+j+1$, matching the next circuit's input count. The embedding theorem for acyclicity (`gatesAcyclic_embedGates`) then shows that the appended gates are acyclic relative to the existing vertices; combining them with the old acyclic list preserves acyclicity (`GatesAcyclic.append`). The output list gains one vertex, so its length becomes $j+1$; the old outputs remain valid and the new output is a vertex of the enlarged circuit. The existing vertex $n$ remains present. Finally, old gates retain their properties by induction, and every embedded gate satisfies the argument conditions by `faninTwo_embedGates`.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.GatesAcyclic.snoc`, `BoolCircuit.GatesAcyclic.append`, `BoolCircuit.gatesAcyclic_embedGates`, `BoolCircuit.length_embedGates`, `BoolCircuit.faninTwo_embedGates`.
