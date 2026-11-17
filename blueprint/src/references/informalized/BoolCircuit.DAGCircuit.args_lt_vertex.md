<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.args_lt_vertex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arguments precede their vertex

**Claim.** If $v$ is a non-input vertex of a finite directed acyclic circuit and lies below the circuit size, then every argument of the gate at position $v-n$ has index strictly less than $v$.

**Proof.** Because $v$ is not an input, $v\ge n$, so the gate position $v-n$ is defined. Since $v<n+\mathrm{length}(C.\mathrm{gates})$, this position lies within the gate list. Acyclicity says each argument of the gate at position $i$ has index less than $n+i$. Substituting $i=v-n$ gives the required strict inequality, namely that every argument is below $v$.
