<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.ExpPoly.of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Pointwise Domination

**Claim.** If $T(n)\le T'(n)$ for every $n$ and $T'$ is exponential-polynomial, then $T$ is exponential-polynomial.

**Proof.** Take witnesses $K,k$ for the exponential-polynomial bound on $T'$. For every $n$, transitivity gives $T(n)\le T'(n)\le 2^{K(n+1)^k}$. The same $K,k$ therefore witness the required bound for $T$.
