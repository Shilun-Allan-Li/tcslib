<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.vertexValue_litVertex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Literal Vertex

**Claim.** In the circuit with one negation gate for each input, the vertex representing the literal true exactly when $x(i)=b$ has value equal to the truth value of $x(i)=b$.

**Proof.** Split according to $b$. If $b$ is false, the literal vertex is at index $n+i$, whose value in this circuit is $!x(i)$ by `BoolCircuit.vertexValue_negInputGates`. For either Boolean value of $x(i)$, this is exactly the truth value of $x(i)=\mathrm{false}$. If $b$ is true, the literal vertex is at index $i$, whose value is $x(i)$ by `BoolCircuit.vertexValue_input`; this is exactly the truth value of $x(i)=\mathrm{true}$. The two cases establish the claim.

**Key facts.** `BoolCircuit.vertexValue_negInputGates`, `BoolCircuit.vertexValue_input`.
