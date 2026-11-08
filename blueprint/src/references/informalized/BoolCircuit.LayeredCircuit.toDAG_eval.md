<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.toDAG_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under DAG Conversion

**Claim.** For every Boolean input assignment, evaluating the DAG obtained from the finite layered circuit and encoding its output in \(\mathrm{Fin}\,2\) gives the same value as evaluating the layered circuit at its unique output.

**Proof.** Apply the layer-by-layer evaluation correspondence (\texttt{BoolCircuit.LayeredCircuit.layerVertex_value}) to the final layer and its unique output node. At this layer, the vertex assigned to that node is the DAG output, and evaluating that vertex using the gates constructed up to the circuit’s depth is exactly the DAG evaluation. The correspondence identifies this value, after encoding the Boolean input assignment in \(\mathrm{Fin}\,2\), with the layered circuit’s evaluation at its output. Since the output type is unique, that evaluation is \(F.\mathrm{eval}_1\).

**Key facts.** `BoolCircuit.LayeredCircuit.layerVertex_value`.
