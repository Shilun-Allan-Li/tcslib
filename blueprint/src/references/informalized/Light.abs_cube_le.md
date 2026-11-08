<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.abs_cube_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for squares and cubes

**Claim.** If $8n+1\le L$ and $i$ is at most the least natural number $r$ such that $n\le r^3$, then $|(i: \mathbb Z)i|\le L$ and $|(i: \mathbb Z)i^2|\le L$.

**Proof.** By monotonicity of cubing and the bound on the least cube root, $i^3\le 8n$. Also $i^2\le i^3$: this is immediate when $i=0$, and when $i>0$ it follows from $1\le i$. Casting these inequalities to the integers gives $(i: \mathbb Z)i^2\le 8n$ and $(i: \mathbb Z)i\le 8n$. Both products are nonnegative. The hypothesis $8n+1\le L$ therefore bounds each product above by $L$; nonnegativity bounds their absolute values below by zero, yielding both asserted absolute-value bounds.

**Key facts.** `Light.cbrtLeast_pow_le`.
