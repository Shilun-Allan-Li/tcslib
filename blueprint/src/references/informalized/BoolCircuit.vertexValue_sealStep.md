<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.vertexValue_sealStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of an Existing Circuit Value

**Claim.** Appending the three gates that negate the value at $u$, disjoin it with the value at index $n+|G|$, and then conjoin the value at $o$ with the value at index $n+|G|+1$ leaves the output value equal to the original value at $o$.

**Proof.** Write $N=n+|G|$, and let $a$ and $b$ be the circuit values at $u$ and $o$. The first appended gate computes $\neg a$ at vertex $N$. The second computes $a\lor\neg a$ at vertex $N+1$, which is true. The third computes $b\land\mathrm{true}$ at vertex $N+2$, hence returns $b$. The existing-value preservation rule says that appending gates does not change values at vertices below the old circuit length plus the number of inputs (`BoolCircuit.vertexValue_append`); the hypotheses on $u$ and $o$ allow it to be applied when reading those values. The rule for the last gate identifies its new vertex value with that gate's evaluation on the preceding circuit (`BoolCircuit.vertexValue_last`), and two-input gate evaluation gives the stated disjunction and conjunction (`BoolCircuit.DAGGate.eval_pair`).

**Key facts.** `BoolCircuit.vertexValue_last`, `BoolCircuit.DAGGate.eval_pair`, `BoolCircuit.vertexValue_append`.
