<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.litV_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Vertex Bound

**Claim.** For every $n,i$ and Boolean value $b$, the literal vertex associated to $n,i,b$ is at most $n+i$.

**Proof.** If $b$ is true, the literal vertex is $i$, which is at most $n+i$. If $b$ is false, it is exactly $n+i$. Thus the bound holds in either case.
