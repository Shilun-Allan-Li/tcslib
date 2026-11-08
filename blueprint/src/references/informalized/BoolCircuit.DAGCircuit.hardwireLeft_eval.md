<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwireLeft_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after left hardwiring

**Claim.** For a circuit $C$ with $m+n$ inputs, fixing the first $m$ inputs to $y$ and evaluating the resulting circuit at $x$ gives the same output as evaluating $C$ at $(y,x)$.

**Proof.** The proof tracks corresponding vertex values through the two circuits. In the original circuit, the input list is ordered as $(y,x)$. In the hardwired circuit, the first $n$ inputs are $x$, followed by $m$ constant gates evaluating to the values in $y$. The index map `leftPerm` sends each of the original first $m$ input positions to the corresponding position after those $n$ inputs, sends each of the remaining $n$ input positions to its position among the hardwired circuit's inputs, and shifts each gate position by $m$. The initial lists therefore agree at corresponding positions. For each original gate, its remapped version reads the same Boolean value at each argument as the original gate; the gate evaluation respects this correspondence (`DAGGate.eval_remap`). Inducting through the gates in topological order preserves the correspondence for every vertex. The general run correspondence result (`BoolCircuit.runWith_remap_rel`) packages this argument, using `leftPerm_lt` to keep mapped vertices within the relevant lists and `leftPerm_gate` for the shifted gate positions. Finally, the hardwired circuit's gates consist of the constant gates followed by the remapped original gates: running the constants appends the values of $y$ (`BoolCircuit.runWith_eval_constGates`), and running the two portions in sequence is governed by `BoolCircuit.runWith_append`. The output vertex is mapped by `leftPerm`, so the corresponding output values agree.

**Key facts.** `BoolCircuit.DAGGate.eval_remap`, `BoolCircuit.DAGCircuit.leftPerm_lt`, `BoolCircuit.DAGCircuit.leftPerm_gate`, `BoolCircuit.runWith_remap_rel`, `BoolCircuit.runWith_append`, `BoolCircuit.runWith_eval_constGates`.
