<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.walkDist_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Walk Distribution

**Claim.** For each nonnegative integer $k$, walking for $k+1$ steps from a rational vertex weight function is equivalent to walking for one step and then for $k$ steps.

**Proof.** Fix a destination vertex $v$. Expand the $(k+1)$-step transition probability from each starting vertex $u$ as a sum over intermediate vertices $x$, using the decomposition of transition probabilities at a successive step (`Randomized.RegularMultigraph.transProb_succ_eq_sum`). In the definition of the walk distribution, multiply these sums by the initial weights and sum over $u$. Interchange the finite sums to group terms by $x$. For each $x$, the inner sum over $u$ is precisely the weight at $x$ after one step, multiplied by the transition probability from $x$ to $v$ in $k$ steps. Summing over $x$ gives the walk distribution after the one-step distribution has itself been walked for $k$ steps.

**Key facts.** `Randomized.RegularMultigraph.transProb_succ_eq_sum`.
