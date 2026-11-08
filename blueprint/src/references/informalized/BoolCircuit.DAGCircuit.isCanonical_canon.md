<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGCircuit.isCanonical_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Form of a Circuit

**Claim.** If the output vertex of a circuit is its last vertex, then its canonicalization has strictly increasing input indices at every gate and still has its output at the last vertex.

**Proof.** For any gate in the canonicalized circuit, membership in the mapped gate list means it is the canonicalization of some original gate. Each such canonicalized gate has its input indices in strictly increasing order (`BoolCircuit.DAGGate.canon_sorted`), proving the first condition of canonicity. Canonicalization preserves circuit size (`BoolCircuit.DAGCircuit.size_canon`); hence the assumed equation between the output index plus one and the size remains true after canonicalization, giving the second condition.

**Key facts.** `BoolCircuit.DAGGate.canon_sorted`, `BoolCircuit.DAGCircuit.size_canon`.
