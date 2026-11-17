<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.vertexValue_negInputGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of Negated Inputs

**Claim.** For each input index $i$, the circuit with one negation gate per input has value $\neg x(i)$ at vertex $n+i$.

**Proof.** The gate at position $i$ is the negation gate reading input vertex $i$. By the rule for evaluating a gate at position $i$ (`BoolCircuit.runWith_getD_gate`), the value at vertex $n+i$ is this gate's evaluation on the values produced by the first $i$ gates. Its evaluation is the negation of the value at vertex $i$. Since $i<n$, the first $i$ gates have not changed the value at that input vertex: it remains the initial input value $x(i)$ (`BoolCircuit.runWith_getD_of_lt`). Thus the value at vertex $n+i$ is $\neg x(i)$.

**Key facts.** `BoolCircuit.runWith_getD_gate`, `BoolCircuit.runWith_getD_of_lt`.
