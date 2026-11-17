<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSplitClause_cursor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting Cursor Monotonicity

**Claim.** For every clause $C$ over natural-number variables and cursor $n$, the cursor returned by splitting $C$ at $n$ is at least $n$.

**Proof.** If $C$ is empty, splitting returns $n$ unchanged, so the claim is equality. If $C$ has a head literal, splitting delegates to the chain construction with that head, the remaining clause, and the same cursor. The chain cursor bound ($\texttt{satChain_cursor}$) gives the required inequality.

**Key facts.** `Complexity.satChain_cursor`.
