<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.toLayered_evalNode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layered nodes agree with circuit execution

**Claim.** At each layer $m$ up to the number of gates, every node's layered-circuit value equals the encoded execution value at its corresponding vertex, using false when that vertex is outside the execution's value list.

**Proof.** Induct on the layer. At layer zero, the nodes are input vertices, and the execution's value list agrees with the input assignment there (`values_getD_input`); the layered evaluation at the initial layer is the input itself (`evalNode_zero`). For the successor step, write the layer as $m+1$. The evaluation recurrence expresses a node's value by applying its layer gate to the preceding layer (`evalNode_succ`). Since $m$ is a valid gate index, the layer construction has two cases. If the node corresponds to an already existing vertex below $n+m$, its layer gate simply copies that preceding-layer node. The induction hypothesis and the fact that converting a node to a vertex and back preserves it (`ofNode_toNode`) give the required equality. Otherwise the node is the new vertex $n+m$. Its execution value is the evaluation of gate $m$ on the execution's value list (`values_getD_gate`). The layer gate applies the corresponding Boolean operation to the preceding-layer values; the gate-evaluation correspondence (`layerGateOf_eval`), together with the induction hypothesis for each argument, identifies this with the encoded execution value. The assumption that no gate is an OR gate is used in that correspondence.

**Key facts.** `BoolCircuit.LayeredCircuit.evalNode_zero`, `BoolCircuit.DAGCircuit.values_getD_input`, `BoolCircuit.LayeredCircuit.evalNode_succ`, `BoolCircuit.DAGCircuit.ofNode_toNode`, `BoolCircuit.DAGCircuit.succ_le`, `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.layerGateOf_eval`.
