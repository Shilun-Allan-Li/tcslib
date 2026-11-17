<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/RunsStayInLimits.lean :: Light.abs_update_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound under a function update

**Claim.** If every value of $f$ and the replacement value $v$ have absolute value at most $B$, then every value of the function obtained by updating $f$ at $x$ to $v$ also has absolute value at most $B$.

**Proof.** At an index $y$, the updated function has value $v$ if $y=x$, and otherwise has value $f(y)$. In the first case the bound is the hypothesis on $v$; in the second it is the hypothesis on $f(y)$.
