<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.SLOperand.vertex_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex Bound for an Operand

**Claim.** If every line operand referenced by an operand $o$ has index less than $i$, then the vertex associated with $o$ is less than $2n+i$.

**Proof.** Consider the three possible forms of $o$. If $o$ is an input $x_k$, its vertex is $k<n$, hence is less than $2n+i$. If it is a negated input, its vertex is $n+k<2n$, and therefore is less than $2n+i$. If it is a line operand with index $j$, the hypothesis says $j<i$, so its vertex $2n+j$ is less than $2n+i$.
