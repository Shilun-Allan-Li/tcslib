<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.vertexValue_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at a Circuit Gate

**Claim.** If gate $j$ exists and all its arguments are among the input vertices and earlier gate vertices, then the value at vertex $n+j$ equals the evaluation of gate $j$ on the full resulting value list.

**Proof.** The value at position $n+j$ in the full run is the evaluation of gate $j$ on the list produced by running only the first $j$ gates (`BoolCircuit.runWith_getD_gate`). To compare this with evaluation on the full run, note that each argument index is less than $n+j$. For every such index, the value in the run of the first $j$ gates agrees with its value in the full run (`BoolCircuit.runWith_getD_take`). Thus the two lists agree wherever gate $j$ reads an argument, and gate evaluation is unchanged when all its argument values agree (`BoolCircuit.DAGGate.eval_congr`).

**Key facts.** `BoolCircuit.runWith_getD_gate`, `BoolCircuit.runWith_getD_take`, `BoolCircuit.DAGGate.eval_congr`.
