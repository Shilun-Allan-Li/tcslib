<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unrollGate_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cases for an Unrolled Gate

**Claim.** At any position $p$, the corresponding unrolled gate either has at most one input and is not a NOT gate, or is a combinational gate with its inputs placed at stage $\lfloor p/s\rfloor$, where $s$ is the sequential circuit's size.

**Proof.** First consider the case where the remainder of $p$ upon division by $s$ is less than the number of registers. The unrolled gate is then either an initial-value gate with no inputs, or a one-input AND gate; neither is a NOT gate. Otherwise, the gate is obtained from the combinational gate list at index $p\bmod s-r$. If this index is in range, that list entry is a gate of the combinational circuit, and the unrolled gate has its kind and its arguments placed at stage $\lfloor p/s\rfloor$. If the index is out of range, the default gate has no inputs and is an AND gate, so it satisfies the first alternative.
