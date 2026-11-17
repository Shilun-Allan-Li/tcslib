<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.litVertex_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal vertex bound

**Claim.** For $i\in\mathrm{Fin}(n)$ and a Boolean polarity $b$, the vertex assigned to the literal is less than $2n$.

**Proof.** If $b$ is true, the assigned vertex is $i$, which is less than $n$ and hence less than $2n$. If $b$ is false, it is $n+i$; since $i<n$, this is less than $n+n=2n$.
