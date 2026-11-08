<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.cbrtLeast_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cube Bound for the Least Cube Root

**Claim.** For every natural number $n$, if $r$ is the least natural number satisfying $n\le r^3$, then $r^3\le 8n$.

**Proof.** Split according to whether $r=0$. In that case the desired inequality is immediate. Otherwise write $r=s+1$. Since $s<r$, the strict bound for numbers below the least cube root gives $s^3<n$ (`pow_lt_of_lt_cbrtLeast`). If $s=0$, the target follows directly. If $s>0$, then $s+1\le 2s$, so monotonicity of cubing gives $(s+1)^3\le(2s)^3=8s^3$. Combining this with $s^3<n$ yields $(s+1)^3\le8n$.

**Key facts.** `Light.pow_lt_of_lt_cbrtLeast`.
