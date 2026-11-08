<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.snapIdx_lt_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot Index Bound

**Claim.** For every $N,T,t\in\mathbb{N}$, writing $k$ for the number of work tapes, one has $t(k(2T+1)+N+3)+k(2T+1)+N+2<(t+1)(k(2T+1)+N+3)$.

**Proof.** Set $S=k(2T+1)+N+3$. The left side is $tS+(S-1)$, because $k(2T+1)+N+2=S-1$. The right side is $(t+1)S=tS+S$, so the inequality reduces to $S-1<S$, which holds for every natural number $S$.
