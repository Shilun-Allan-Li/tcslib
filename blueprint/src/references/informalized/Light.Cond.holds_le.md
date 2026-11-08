<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Cond.holds_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Meaning of the Less-Than-or-Equal Condition

**Claim.** For a state $\sigma$ and expressions $a,b$, the condition written $a\le' b$ holds in $\sigma$ if and only if the value of $a$ in $\sigma$ is at most the value of $b$ in $\sigma$.

**Proof.** By the definition of the notation $a\le' b$, its truth in $\sigma$ is the strict inequality $a.val\,\sigma < b.val\,\sigma+1$. For integers, $x<y+1$ is equivalent to $x\le y$ (`Int.lt_add_one_iff`). Applying this equivalence to the two expression values proves the claim.
