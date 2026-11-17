<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.toLayered_onlyUsesGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate operations in the layered circuit

**Claim.** Every gate operation in the layered circuit associated to a well-formed DAG circuit is the identity, NOT, or an unbounded fan-in AND operation.

**Proof.** Fix a layer and a node in that layer. The construction of its gate has three branches. If the layer index is below the number of gates and the node is already among the earlier vertices, the gate is the identity. If the layer index is below the number of gates but the node is the new vertex, its operation is obtained from the corresponding DAG gate; the well-formedness hypothesis ensures that this operation is among the standard gate operations (the membership fact `layerGateOf_mem`). Finally, if the index is past the gates, the construction again uses the identity. In every branch the operation belongs to the specified set of standard operations.

**Key facts.** `BoolCircuit.layerGateOf_mem`.
