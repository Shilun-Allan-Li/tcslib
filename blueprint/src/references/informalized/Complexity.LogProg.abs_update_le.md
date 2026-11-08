<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.abs_update_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute-Value Bound Under Update

**Claim.** If every value of $D$ and the replacement value $v$ have absolute value at most $B$, then every value of the function obtained by replacing $D(i)$ by $v$ also has absolute value at most $B$.

**Proof.** Fix an index $j$. If $j=i$, the updated value is $v$, so the desired bound is the hypothesis on $v$. If $j\ne i$, the update leaves the value at $j$ unchanged, and the desired bound follows from the bound on $D(j)$.
