<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ZeroSumGame.lean :: weak_duality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak duality for finite games

**Claim.** For any mixed strategies $p$ and $q$ in a finite zero-sum game, the smallest payoff against a pure column is at most the largest payoff against a pure row.

**Proof.** Let $v=\sum_i\sum_j p_iA_{ij}q_j$ be the payoff averaged over both mixed strategies. First rewrite this as $\sum_j (\sum_i p_iA_{ij})q_j$. Each pure-column payoff is at least their infimum, and each $q_j$ is nonnegative; since the weights $q_j$ sum to $1$, this weighted average is at least the infimum. Thus $\inf_j\sum_i p_iA_{ij}\le v$. Next rewrite $v$ as $\sum_i (\sum_j A_{ij}q_j)p_i$. Each pure-row payoff is at most their supremum, and the weights $p_i$ are nonnegative and sum to $1$, so this average is at most the supremum. Hence $v\le\sup_i\sum_j A_{ij}q_j$. Combining the inequalities proves the claim. The payoff bounds ensure the relevant infimum and supremum are bounded, as needed for these comparisons.
