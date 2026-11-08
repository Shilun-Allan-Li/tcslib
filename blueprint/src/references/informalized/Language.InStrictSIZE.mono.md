<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: Language.InStrictSIZE.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of strict circuit size bounds

**Claim.** If a language has a strict circuit family of size at most $T(n)$ and $T(n)\le T'(n)$ at every input length, it has a strict circuit family of size at most $T'(n)$.

**Proof.** Choose the strict family witnessing the bound $T$ and retain it unchanged, including its strictness conditions and recognized language. At each length $n$, its size is at most $T(n)$, hence at most $T'(n)$. Therefore this family witnesses the new bound.
