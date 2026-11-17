<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Stmt.width_seq_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bound for sequential composition

**Claim.** The sequential composition of $s$ and $t$ has width at most $F$ exactly when each of $s$ and $t$ has width at most $F$.

**Proof.** The width of the sequential composition is the maximum of the widths of $s$ and $t$. This maximum is at most $F$ precisely when both widths are at most $F$.
