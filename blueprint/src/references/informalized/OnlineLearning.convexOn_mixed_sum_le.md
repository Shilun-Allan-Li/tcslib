<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.convexOn_mixed_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jensen Inequality for Convex Functions

**Claim.** For a convex function on $S$, its value at the weighted sum of points in $S$ is at most the weighted sum of its values, when the weights are nonnegative and sum to one.

**Proof.** Apply the finite weighted-sum inequality for a convex function: the function of a weighted average is at most the weighted average of the function values. The points $x_i$ lie in $S$, and the mixed-strategy weights are nonnegative and sum to one, so the inequality applies. Rewriting scalar multiplication as ordinary multiplication yields the displayed statement.
