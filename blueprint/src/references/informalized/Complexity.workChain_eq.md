<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.workChain_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Chain Recurrence

**Claim.** At position $z$, the work-chain value is the contents of cell $z$ when the tape head is at $z$; otherwise it is the work-chain value at $z-1$.

**Proof.** Unfold the work-chain definition and split according to whether the head position equals $z$. If it does, the condition that the head position is at most $z$ holds, so the left side is the scanned symbol, which is exactly the contents of cell $z$. The first alternative on the right also selects those contents. If the head position is not $z$, split according to whether it is at most $z-1$. In that case, the chain at $z-1$ has the scanned symbol, and the head position is also at most $z$, so the chain at $z$ has that same value; the conditional on the right selects the chain at $z-1$. If the head position is not at most $z-1$, then it is greater than $z-1$ and, since it is not equal to $z$, it is greater than $z$. Both chain values are therefore none, and the right-hand conditional selects the chain at $z-1$.
