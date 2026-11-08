<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.vertexValue_not_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Negation Gate

**Claim.** If gate $i$ reads vertex $w$, is a negation gate, and $w<n+i$, then the value at vertex $n+i$ is the negation of the value at vertex $w$.

**Proof.** The value at vertex $n+i$ is the evaluation of gate $i$ on the values produced by the first $i$ gates (`BoolCircuit.runWith_getD_gate`). By hypothesis this gate is a negation gate reading $w$, so its evaluation is the negation of the value at $w$ in that prefix evaluation. The inequality $w<n+i$ ensures that this value agrees with the value at $w$ after all gates have run: the prefix and full circuit give the same value at every vertex below $n+i$ (`BoolCircuit.runWith_getD_take`). This gives the claimed equality.

**Key facts.** `BoolCircuit.runWith_getD_gate`, `BoolCircuit.runWith_getD_take`.
