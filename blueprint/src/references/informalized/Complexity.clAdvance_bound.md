<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clAdvance_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Advanced Movement Counts

**Claim.** If every count is at most $t$, then after increasing each count selected by the sign vector by one, every resulting count is at most $t+1$.

**Proof.** Fix a doubled coordinate. Its new count is its old count plus either zero or one, according as it is unselected or selected. Since the old count is at most $t$, the new count is at most $t+1 in either case.
