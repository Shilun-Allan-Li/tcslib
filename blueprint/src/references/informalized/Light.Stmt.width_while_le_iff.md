<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Stmt.width_while_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# While loop width bound

**Claim.** The width of a while loop with condition $c$ and body $s$ is at most $F$ exactly when the widths of $c$ and $s$ are each at most $F$.

**Proof.** The loop width is the maximum of the condition width and body width. A maximum of two natural numbers is at most $F$ if and only if both numbers are at most $F$.
