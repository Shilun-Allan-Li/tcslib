<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unroll_reg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Values in the Unrolled Circuit

**Claim.** For each stage $k\le T$ and register $j$, the value at its placed vertex equals the evaluation of the corresponding initial-value gate when $k=0$, or the one-input AND gate reading its next-state source at stage $k-1$ when $k>0$.

**Proof.** The register offset $j$ is less than the sequential circuit's size. Thus position $sk+j$ lies within the unrolled gate list, whose length is $(T+1)s$; here we use $k\le T$. The placed register vertex has index $n+sk+j$. The DAG gate-value property (`DAGCircuit.values_getD_gate`) identifies its value with the evaluation of the gate at position $sk+j$. Division with remainder (`div_mod_block`) says this position is in stage $k$ at register offset $j$. The definition of the unrolled gate at a register offset then gives the initial-value gate if $k=0$, and otherwise the one-input AND gate whose input is the placed next-state source at stage $k-1$.

**Key facts.** `BoolCircuit.SeqCircuit.length_unroll_gates`, `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.SeqCircuit.div_mod_block`, `BoolCircuit.SeqCircuit.getElem_unroll_gates`.
