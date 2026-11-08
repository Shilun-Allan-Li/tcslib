<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.value_litV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of Literal Vertices

**Claim.** For an input bit $x_i$ and a Boolean sign $b$, the literal vertex has value true exactly when $x_i=b$.

**Proof.** First, the input vertex $i$ has value $x_i$ by the input-vertex property (`BoolCircuit.vertexValue_input`). If $b$ is true, the literal vertex is $i$, so its value is $x_i$, which is true exactly when $x_i$ is true. If $b$ is false, the literal vertex is $n+i$. The offset identities (`BoolCircuit.Lupanov.offsets`) show that the corresponding gate lies within the circuit, so the gate-value theorem (`BoolCircuit.Lupanov.value_gateAt`) identifies its value with the gate at position $i$. Since $i<n$, that gate is a NOT gate reading input vertex $i$; its value is therefore the negation of $x_i$. This is true exactly when $x_i$ is false, as required.

**Key facts.** `BoolCircuit.vertexValue_input`, `BoolCircuit.Lupanov.offsets`, `BoolCircuit.Lupanov.value_gateAt`.
