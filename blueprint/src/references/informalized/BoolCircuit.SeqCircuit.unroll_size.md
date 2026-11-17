<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unroll_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Unrolled Circuit

**Claim.** For every $T$, the unrolling has size $n+(T+1)$ times the sequential circuit's size.

**Proof.** By definition, the size of a DAG circuit is its number of inputs plus its number of gates. The unrolled gate list has length $(T+1)$ times the sequential circuit's size (`length_unroll_gates`). Substituting this length into the DAG size formula gives $n+(T+1)\,\mathrm{size}(M)$.

**Key facts.** `BoolCircuit.SeqCircuit.length_unroll_gates`.
