<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/DirectedWalk.lean :: Randomized.hitTime_chainDigraph_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on Chain Hitting Time

**Claim.** If the expected truncated hitting time of the last vertex in the chain digraph, starting from vertex $0$, is at most $B$ for every truncation length, then $(2^n-1)/2\le B$.

**Proof.** Set $M=2^n$ and use the assumed bound at truncation length $M$. For each $j<M$, the chain hitting-probability bound gives $\Pr(\text{hit by step }j)\le (j+1)/M$. Hence each summand $1-\Pr(\text{hit by step }j)$ in the truncated hitting time is at least $1-(j+1)/M$. Summing these inequalities shows that the truncated hitting time at $M$ is at least $\sum_{j=0}^{M-1}(1-(j+1)/M)$. The sum of the first $M$ positive integers is $M(M+1)/2$, so this expression equals $M-(M+1)/2=(M-1)/2$. Combining this lower bound with the assumed upper bound $B$ proves the result. Here the pointwise chain estimate is `Randomized.hitProb_chainDigraph_le`, and the sum formula is `Randomized.sum_range_succ_cast`.

**Key facts.** `Randomized.hitProb_chainDigraph_le`, `Randomized.sum_range_succ_cast`.
