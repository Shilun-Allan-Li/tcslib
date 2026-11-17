<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: Language.InTreeSize.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of tree size bounds

**Claim.** If a language has tree circuits of size at most $T(n)$ at every input length and $T(n)\le T'(n)$ for every $n$, then it has tree circuits of size at most $T'(n)$ recognizing the same language.

**Proof.** Use the same circuit family that witnesses the size bound $T$. At each input length, its size is at most $T(n)$ and hence at most $T'(n)$. Its acceptance condition is unchanged, so it still recognizes the language.
