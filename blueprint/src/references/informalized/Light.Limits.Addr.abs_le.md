<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Limits.Addr.abs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Bound for an Address

**Claim.** If an address $a$ is nonnegative and strictly below the space bound $S$, and $S\le W$, then $|a|\le W$.

**Proof.** Because $a\ge0$, its absolute value is $a$. The address condition also gives $a<S$, hence $a\le S$. Combining this with $S\le W$ yields $|a|=a\le W$.
