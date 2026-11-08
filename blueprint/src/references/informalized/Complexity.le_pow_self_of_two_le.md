<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.le_pow_self_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural numbers bounded by powers

**Claim.** For natural numbers $m,n$ with $2\le n$, one has $m\le n^m$.

**Proof.** The standard bound $m<2^m$ holds for every natural number $m$. Since $2\le n$, monotonicity of the natural-number power in its base gives $2^m\le n^m$. Combining these inequalities proves $m\le n^m$.
