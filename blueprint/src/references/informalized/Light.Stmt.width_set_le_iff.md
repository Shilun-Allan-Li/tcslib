<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Stmt.width_set_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment width bound

**Claim.** The width of an assignment to variable $x$ with expression $e$ is at most $F$ exactly when $x<F$ and $e$ has width at most $F$.

**Proof.** The assignment width is the maximum of $x+1$ and the width of $e$. A maximum is at most $F$ exactly when both entries are at most $F$; for natural numbers, $x+1\le F$ is equivalent to $x<F$.
