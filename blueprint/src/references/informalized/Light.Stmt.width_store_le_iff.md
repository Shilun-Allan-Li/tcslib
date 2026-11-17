<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Stmt.width_store_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory store width bound

**Claim.** The width of a memory store with address expression $a$ and value expression $e$ is at most $F$ exactly when each expression has width at most $F$.

**Proof.** The store width is the maximum of the widths of $a$ and $e$. This maximum is at most $F$ precisely when each of its two entries is at most $F$.
