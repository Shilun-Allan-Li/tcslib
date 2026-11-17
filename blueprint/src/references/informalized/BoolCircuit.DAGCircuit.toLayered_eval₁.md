<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.toLayered_eval₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layered-circuit output agrees with circuit evaluation

**Claim.** For every Boolean input assignment, the value of the associated layered circuit equals the encoded output value of the DAG circuit.

**Proof.** Consider the unique node in the final layer, whose type is the singleton output type. The layered-circuit evaluation recurrence at the successor layer reduces its value to the output selected by the final layer gate (`evalNode_succ`). At this last layer the index is not a gate index, so the layer gate copies the circuit's designated output vertex. The layer-node evaluation theorem at layer $|C.gates|$ identifies that vertex's layered value with its execution value; conversion between the layer node and vertex is inverse (`ofNode_toNode`). By definition, the execution value at the designated output is the circuit's evaluation. Encoding it in $\mathrm{Fin}\,2$ gives the claimed equality.

**Key facts.** `BoolCircuit.LayeredCircuit.evalNode_succ`, `BoolCircuit.DAGCircuit.toLayered_evalNode`, `BoolCircuit.DAGCircuit.ofNode_toNode`.
