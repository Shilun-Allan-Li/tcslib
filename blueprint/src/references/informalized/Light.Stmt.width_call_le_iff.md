<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Stmt.width_call_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bound for a procedure call

**Claim.** A procedure call with target variable $x$ and argument list $A$ has width at most $F$ exactly when $x<F$, the argument count is at most $F$, and every argument has width at most $F$.

**Proof.** By definition, the call's width is the maximum of $x+1$, the length of the argument list, and the maximum argument width. A maximum of natural numbers is at most $F$ exactly when each entry is at most $F$. The argument-list maximum is at most $F$ exactly when each listed expression has width at most $F$ (`Light.maxOf_le_iff`). Finally, $x+1\le F$ is equivalent to $x<F$. Combining these conditions gives the equivalence.

**Key facts.** `Light.maxOf_le_iff`.
