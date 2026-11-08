<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Expr.width_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expression Width Bound

**Claim.** For every expression $e$ and natural number $F$, its width is at most $F$ if and only if both its variable bound and its height are at most $F$.

**Proof.** The width is the maximum of the expression's variable bound and height. This maximum is at most $F$ precisely when each of those two quantities is at most $F$.
