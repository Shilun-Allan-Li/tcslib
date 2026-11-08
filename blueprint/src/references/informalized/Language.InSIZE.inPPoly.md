<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: Language.InSIZE.inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial size from a size bound

**Claim.** If a language has fan-in-two circuits of size at most $T(n)$ and $T(n)\le a(n+1)^k$ for all $n$, then it has polynomial-size fan-in-two circuits.

**Proof.** By the hypothesis that the language belongs to the size class for $T$, choose a circuit family that recognizes it, has fan-in at most two, and has size at most $T(n)$ at each length. Monotonicity of circuit size bounds (`Language.InSIZE.mono`) keeps this same family and recognition property while replacing the bound $T(n)$ by $a(n+1)^k$. The coefficients $a,k$ therefore witness polynomial size.

**Key facts.** `Language.InSIZE.mono`.
