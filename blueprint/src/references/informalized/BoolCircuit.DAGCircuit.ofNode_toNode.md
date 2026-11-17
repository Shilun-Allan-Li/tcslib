<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.ofNode_toNode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse layer-index conversion

**Claim.** For a layer index $d$ no greater than the number of gates, converting an index in $0,\ldots,n+d-1$ to its layer vertex and then back to an index returns the original index.

**Proof.** Under the stated bound on $d$, the layer's vertices are identified with the indices in $\mathrm{Fin}(n+d)$. The conversion to a vertex and the conversion back use the same identification, so their composite is the identity on each index.
