<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.payoffVsPure_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Mixed Payoff

**Claim.** When all game payoffs are nonnegative, a mixed row strategy's expected payoff against any fixed pure column is nonnegative.

**Proof.** For every row $i$, both the strategy weight $p_i$ and the payoff in column $j$ are nonnegative. Their product is therefore nonnegative, and the sum of these products over all rows is nonnegative.
