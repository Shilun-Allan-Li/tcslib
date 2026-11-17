<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.b2f_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation under Boolean encoding

**Claim.** For every Boolean $a$, the encoding of its negation in $\mathrm{Fin}(2)$ equals $1$ minus the encoding of $a$.

**Proof.** There are only two possibilities for $a$. If $a$ is false, its negation is true, and the two sides both equal $1$. If $a$ is true, its negation is false, and both sides equal $0$.
