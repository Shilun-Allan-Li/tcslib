<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/ConvexPrediction.lean :: hedgePrediction_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of Hedge Predictions

**Claim.** If every expert prediction lies in the convex set $S$, then Hedge’s weighted-average prediction at every round also lies in $S.

**Proof.** At a fixed round, Hedge’s prediction is the finite weighted sum of the expert predictions. Its weights are nonnegative (`hedgeDist_nonneg`) and sum to one (`hedgeDist_sum`). The defining closure property of a convex set under finite convex combinations then places this prediction in $S.

**Key facts.** `hedgeDist_nonneg`, `hedgeDist_sum`.
