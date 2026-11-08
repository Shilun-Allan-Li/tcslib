<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unroll_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values Within an Unrolled Stage

**Claim.** If every register vertex at stage $k$ in the unrolled circuit has its prescribed state value, then each placed vertex corresponding to a valid input, register, or combinational gate has the same value as that vertex in the combinational circuit evaluated on the input and the state at time $k$.

**Proof.** Fix $k\le T$ and use strong induction on the vertex index $a$, proving the claim for every smaller index so that earlier gate inputs are covered. If $a<n$, it is an input: placing it leaves its index unchanged, and the input-value property for DAG evaluation identifies its value with $x(a)$. The combinational circuit's value at that input is also $x(a)$. If $n\le a<n+r$, write $a=n+j$ for a register $j$. The assumed register-value condition gives its value in the unrolling as the state at time $k$; the combinational circuit's corresponding input is that same register value. Finally, if $a\ge n+r$, write $a=n+r+i$, where $i$ indexes a combinational gate. Its placed vertex is the gate at position $sk+r+i$ in the unrolled gate list. Since $r+i<s$, division with remainder identifies this position as stage $k$, offset $r+i$; the gate-list indexing property therefore identifies the gate with combinational gate $i$, with each argument placed at stage $k$. The DAG gate remapping identity (`DAGGate.eval_remap`) reduces equality of these gate values to equality at the placed arguments. Every such argument is earlier than gate $i$ by the combinational circuit's acyclicity condition, so the induction hypothesis applies. The combinational gate-value property (`DAGCircuit.values_getD_gate`) then identifies the resulting value with the combinational circuit's value at index $a$.

**Key facts.** `BoolCircuit.DAGCircuit.values_getD_input`, `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.DAGGate.eval_remap`, `BoolCircuit.SeqCircuit.div_mod_block`, `BoolCircuit.SeqCircuit.getElem_unroll_gates`, `BoolCircuit.SeqCircuit.length_unroll_gates`.
