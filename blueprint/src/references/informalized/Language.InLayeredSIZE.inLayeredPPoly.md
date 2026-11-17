<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: Language.InLayeredSIZE.inLayeredPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound for Layered Size

**Claim.** If a language has a layered-circuit family of size at most $T(n)$ and $T(n)\le a(n+1)^k$ for all $n$, then it has layered polynomial size with parameters $a,k$.

**Proof.** By hypothesis, the same finite layered-circuit family uses only the allowed standard gates, recognizes the language, and has size at most $T(n)$ at every input length. The pointwise inequality $T(n)\le a(n+1)^k$ transfers that size bound directly to the same family. It therefore witnesses layered polynomial size with the given parameters (`Language.InLayeredSIZE.mono`).

**Key facts.** `Language.InLayeredSIZE.mono`.
