<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.payoffVsPure_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payoff Upper Bound Against a Pure Column

**Claim.** In a game whose payoffs are at most one, a mixed row strategy's expected payoff against any fixed pure column is at most one.

**Proof.** For each row $i$, the payoff in column $j$ is at most $1$. Multiplying this inequality by the nonnegative weight $p_i$ preserves it, so summing over rows bounds the expected payoff by $\sum_i p_i\cdot 1$. Since the strategy weights sum to one, this upper bound is $1$.
