<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.pureVsPayoff_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payoff Upper Bound Against a Mixed Column

**Claim.** If every game payoff is at most one, the expected payoff of any fixed pure row against a mixed column strategy is at most one.

**Proof.** For each column $j$, the payoff of row $i$ is at most $1$. Multiplying by the nonnegative weight $q_j$ preserves the inequality. Summing over columns bounds the expected payoff by $\sum_j 1\cdot q_j$, which equals $1$ because the strategy weights sum to one.
