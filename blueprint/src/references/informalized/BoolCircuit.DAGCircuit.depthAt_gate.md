<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuit.depthAt_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a Gate

**Claim.** For a gate at index $i$, its vertex depth is one plus the maximum of zero and the depths of the vertices read by that gate, with out-of-range depth lookups interpreted as zero.

**Proof.** The depth list is obtained by starting with $n$ zeros and appending, in order, the depth computed for each gate from the list available before that gate. Since $i$ is a valid gate index, the depth at position $n+i$ in the full list is therefore the depth of gate $i$ evaluated on the list produced by processing only the first $i$ gates (`runWith_getD_gate`). For each argument $a$ of gate $i$, the circuit's topological-order condition gives $a<n+i$. Thus the lookup at position $a$ is the same in that initial list and in the full depth list: processing the first $i$ gates preserves every lookup below $n+i$ (`runWith_getD_take`). The two lists consequently give the gate the same depth, proving the claimed formula.

**Key facts.** `BoolCircuit.runWith_getD_gate`, `BoolCircuit.runWith_getD_take`, `BoolCircuit.DAGGate.depth_congr`.
