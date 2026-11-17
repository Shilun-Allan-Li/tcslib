<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.concaveOn_le_mixed_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jensen Inequality for Concave Functions

**Claim.** For a concave function on $S$, the weighted sum of its values at points of $S$ is at most its value at the weighted sum of those points, when the weights are nonnegative and sum to one.

**Proof.** Apply the finite weighted-sum inequality for a concave function: for points in its domain and nonnegative weights with total weight one, the function of the weighted average is at least the weighted average of the function values. Here the points are $y_j\in S$, and the mixed-strategy weights satisfy precisely those conditions. Writing scalar multiplication by a real weight as ordinary multiplication gives the stated inequality.
