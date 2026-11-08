<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satChain_cursor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Chain Cursor

**Claim.** For every head literal, remainder, and natural number $n$, the cursor returned by the clause-splitting chain is at least $n$.

**Proof.** Induct on the remainder. If it has fewer than three literals, the chain does not advance the cursor, so the returned value is $n$. Otherwise the chain recurses with cursor $n+1$ on a shorter remainder. By induction, that recursive call returns a cursor at least $n+1$, hence at least $n$.
