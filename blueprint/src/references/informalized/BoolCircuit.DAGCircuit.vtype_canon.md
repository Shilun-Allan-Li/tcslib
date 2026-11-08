<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGCircuit.vtype_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex types under canonicalization

**Claim.** For every circuit $C$ and vertex index $i$, the gate type at $i$ in the canonicalized circuit equals the gate type at $i$ in $C$.

**Proof.** Expand the definition of vertex type in both circuits. If $i<n$, both types are absent. Otherwise, canonicalization preserves the gate list at the corresponding index; mapping the gate-kind projection over the optional indexed gate therefore gives the same optional type. The two cases establish the equality.
