<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.IsStrict.output_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output is the last vertex

**Claim.** The output vertex of a strict circuit $C$ has index $\mathrm{size}(C)-1$.

**Proof.** Suppose instead that the output differs from the vertex of index $\mathrm{size}(C)-1$. This last index is a valid vertex, and strictness therefore gives it positive fan-out. But the acyclicity of the gate list implies that any vertex at or beyond the last gate has fan-out zero (`fanoutIn_last_eq_zero`): every gate reads only earlier vertices. Since $\mathrm{size}(C)=n+\mathrm{length}(C.\mathrm{gates})$, the vertex of index $\mathrm{size}(C)-1$ is at or beyond that final gate. The resulting contradiction proves the equality.

**Key facts.** `BoolCircuit.fanoutIn_last_eq_zero`.
