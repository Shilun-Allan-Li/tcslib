<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: Language.InSIZE.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of circuit size bounds

**Claim.** If a language is recognized by fan-in-two circuits of size at most $T(n)$ and $T(n)\le T'(n)$ at every input length, the same language is recognized by fan-in-two circuits of size at most $T'(n)$.

**Proof.** Take a family witnessing the size bound $T$. Keep that family, its fan-in-two property, and its recognized language unchanged. For each input length, its size is at most $T(n)$, which is at most $T'(n)$ by hypothesis. Hence it witnesses the claimed bound.
