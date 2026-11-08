<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: Language.InLayeredSIZE.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Layered Circuit Size

**Claim.** If a language has an allowed finite layered-circuit family of size at most $T(n)$ and $T(n)\le T'(n)$ for every $n$, then it has such a family of size at most $T'(n)$.

**Proof.** Use the family that witnesses the bound $T$. It already has the required finiteness, gate restrictions, and language. At each input length, its size is at most $T(n)$, which is at most $T'(n)$ by assumption. The same family therefore witnesses the enlarged bound.
