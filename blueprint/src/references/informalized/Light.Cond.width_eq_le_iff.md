<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Cond.width_eq_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality Condition Width Bound

**Claim.** For expressions $a,b$ and a natural number $F$, the width of the equality condition comparing $a$ and $b$ is at most $F$ if and only if both $a$ and $b$ have width at most $F$.

**Proof.** The width of the equality condition is the maximum of the widths of its two expressions. A maximum is at most $F$ exactly when each of its entries is at most $F$. This gives the stated equivalence.
