<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_choice_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the padded exponential budget

**Claim.** For natural numbers $a,c,n$, one has $a\cdot2^{n^c}\le a\cdot2^{(n+1)^c}$.

**Proof.** Since $n\le n+1$, monotonicity of the $c$th power gives $n^c\le(n+1)^c$. Raising $2$ to these exponents preserves the inequality, and multiplying both sides by the nonnegative number $a$ gives the result.
