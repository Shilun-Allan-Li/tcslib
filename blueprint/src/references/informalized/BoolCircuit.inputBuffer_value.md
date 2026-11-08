<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.inputBuffer_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values Produced by an Input Buffer

**Claim.** For each buffer position $i$, the value at index $n+i$ after evaluating the input buffer on the input list is the value selected by source position $i$.

**Proof.** The list of buffer gates has length $m$, so $i$ is a valid gate position. The run-with-gates indexing formula (`runWith_getD_gate`) identifies the value at index $n+i$ with the evaluation of gate $i$ using the values produced by the preceding gates. The gate at that position is exactly the gate associated with $s(i)$. If $s(i)$ selects an input $j$, this gate reads position $j$; since $j<n$, the earlier run has not changed that position, by the fact that running gates preserves every initial-list index in range (`runWith_getD_of_lt`). Thus the gate returns the original input value $x(j)$. If $s(i)$ selects a constant $b$, the associated empty-argument AND gate evaluates to true when $b$ is true, and the empty-argument OR gate evaluates to false when $b$ is false. In either case the result is precisely the value selected by $s(i)$.

**Key facts.** `BoolCircuit.runWith_getD_gate`, `BoolCircuit.runWith_getD_of_lt`.
