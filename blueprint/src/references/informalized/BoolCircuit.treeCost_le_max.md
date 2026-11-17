<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.treeCost_le_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree Cost Bound

**Claim.** For natural numbers $m$ and $k$ with $m\le k$, the tree cost of $m$ is at most $\max(1,k-1)$.

**Proof.** If $m=0$, its tree cost is $1$, and the maximum on the right is at least $1$. If $m>0$, the tree cost is $m-1$. Since $m\le k$, this is at most $k-1$, and hence at most $\max(1,k-1)$.
