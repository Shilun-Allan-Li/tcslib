<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.encodeCircuit_node -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding an Internal Circuit Node

**Claim.** For any natural number $n$, gate choice $b$, and list $C$ of circuit trees on $n$ variables, the encoding of the node with gate choice $b$ and children $C$ is the bit $1$, followed by $b$, followed by the encoding of $C$.

**Proof.** The node encoding begins with the bit $1$ and the gate choice $b$, then concatenates the marked encoding of each child, and finally appends the terminator $[0]$. The encoding of the child list is defined by exactly that child concatenation followed by the same terminator. Substituting this definition gives the claimed expression.
