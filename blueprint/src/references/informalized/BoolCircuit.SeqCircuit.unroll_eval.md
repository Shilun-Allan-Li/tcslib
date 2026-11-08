<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unroll_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Unrolled Circuit

**Claim.** For every time bound $T$ and input $x$, evaluating the circuit unrolled through time $T$ gives the sequential circuit's output at time $T$.

**Proof.** Apply the stage-value theorem `unroll_values` with stage $k=T$ and vertex $a$ equal to the combinational circuit's output. Its hypotheses hold: $T\le T$, and the required register values at that stage are supplied by the theorem's established register-value condition. The conclusion equates the value at the placed output vertex in the unrolled DAG with the combinational circuit's value on the input together with the state at time $T$. By definition, these are respectively the unrolled circuit's evaluation and the sequential circuit's run at time $T$.

**Key facts.** `BoolCircuit.SeqCircuit.unroll_values`.
