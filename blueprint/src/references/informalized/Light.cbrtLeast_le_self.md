<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.cbrtLeast_le_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Least Cube Root Bounded by Input

**Claim.** For every natural number $n$, the least natural number $r$ satisfying $n\le r^3$ is at most $n$.

**Proof.** Apply the least cube-root bound `cbrtLeast_le` with $s=n$. The required premise $n\le n^3$ holds because $n\le n^3$ for every natural number when the exponent is $3$. This gives $r\le n$.

**Key facts.** `Light.cbrtLeast_le`.
