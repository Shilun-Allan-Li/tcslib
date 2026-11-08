<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.pureVsPayoff_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Pure-Row Expected Payoff

**Claim.** When the payoffs are nonnegative, the expected payoff of a fixed pure row against a mixed column strategy is nonnegative.

**Proof.** For every column $j$, the payoff of row $i$ and the strategy weight $q_j$ are nonnegative, so their product is nonnegative. Summing these products over all columns gives a nonnegative expected payoff.
