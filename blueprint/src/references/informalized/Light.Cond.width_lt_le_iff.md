<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Cond.width_lt_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Inequality Condition Width Bound

**Claim.** For expressions $a,b$ and a natural number $F$, the width of the strict-inequality condition comparing $a$ and $b$ is at most $F$ if and only if both $a$ and $b$ have width at most $F$.

**Proof.** The width of the strict-inequality condition is the maximum of the widths of its two expressions. By the characterization of a maximum, this is at most $F$ exactly when both expression widths are at most $F$.
