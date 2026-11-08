<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.value_gateAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Circuit Gate

**Claim.** For every gate position $j<\mathrm{total}(n,k)$, the value at vertex $n+j$ is the evaluation of the gate at position $j$ on the resulting list of vertex values.

**Proof.** The length of the gate list is $\mathrm{total}(n,k)$, so the stated bound places $j$ within the list. The vertex-value evaluation principle says that the value at vertex $n+j$ is the evaluation of the gate stored at list position $j$, provided each of that gate's input vertices precedes it. The input-bound lemma gives exactly this condition for the gate at position $j$ (gateAt_args_lt). Finally, the list-entry lemma identifies the gate stored there with the gate specified by the position function (getElem_gates), yielding the assertion.

**Key facts.** `BoolCircuit.Lupanov.vertexValue_gate`, `BoolCircuit.Lupanov.gateAt_args_lt`, `BoolCircuit.Lupanov.getElem_gates`.
