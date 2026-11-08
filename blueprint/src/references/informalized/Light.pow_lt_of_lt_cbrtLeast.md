<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.pow_lt_of_lt_cbrtLeast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cube Bound Below the Least Cube Root

**Claim.** If $s$ is less than the least natural number whose cube is at least $n$, then $s^3<n$.

**Proof.** The least cube root is defined as the least natural number satisfying $n\le r^3$, and such a number exists (`Light.exists_le_cube`). By minimality, every $s$ strictly below it fails that property: it is not the case that $n\le s^3$. The linear order on the natural numbers turns this into $s^3<n$.

**Key facts.** `Light.exists_le_cube`.
