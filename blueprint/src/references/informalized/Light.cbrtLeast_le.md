<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.cbrtLeast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Least Cube-Root Bound

**Claim.** If $n\le s^3$, then the least natural number $r$ satisfying $n\le r^3$ is at most $s$.

**Proof.** By definition, the least cube root is the least natural number satisfying the property $n\le r^3$. The existence fact `exists_le_cube` supplies a witness that this property is attainable. Since $s$ also satisfies it by hypothesis, the least such natural number is at most $s, as expressed by the minimum property of the natural-number least-witness operator.

**Key facts.** `Light.exists_le_cube`.
