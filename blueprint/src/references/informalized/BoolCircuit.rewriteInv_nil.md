<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.rewriteInv_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant for the Empty Gate List

**Claim.** For any $n,c$ and gate property $P$, the empty original list with the identity map on the $n$ inputs satisfies the rewriting invariant.

**Proof.** With no gates, the initial and rewritten gate lists are both empty, and the map is the range of the input indices, so it has length $n$ and sends each input index $v<n$ to $v$. The empty list is acyclic (`GatesAcyclic.nil`), has length zero, and vacuously satisfies the gate property. For values, each mapped input vertex has value $x(v)$ by the input-value fact (`vertexValue_input`), which is exactly the value at that vertex in the empty original circuit. For depths, every input has depth zero (`vertexDepth_input`) in both circuits, so the depth inequality holds.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.vertexValue_input`, `BoolCircuit.vertexDepth_input`.
