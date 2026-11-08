<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Limits.abs_le_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Bound Below the Space Limit

**Claim.** If $S\le W$ and a natural number $x$ satisfies $x\le S$, then the absolute value of $x$, viewed as an integer, is at most $W$.

**Proof.** The integer cast of $x$ is nonnegative, so its absolute value is just $x$ viewed as an integer. Casting the inequality $x\le S$ gives $(x: \mathbb Z)\le(S: \mathbb Z)$. Transitivity with $(S: \mathbb Z)\le W$ proves the bound.
