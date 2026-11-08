<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Stmt.width_ite_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bound for a conditional

**Claim.** A conditional statement with condition $c$ and branches $s,t$ has width at most $F$ exactly when the widths of $c$, $s$, and $t$ are each at most $F$.

**Proof.** By definition, the conditional's width is the maximum of the condition's width and the maximum of the two branch widths. A maximum is at most $F$ exactly when each of its entries is at most $F$. Applying this twice gives the three stated bounds.
