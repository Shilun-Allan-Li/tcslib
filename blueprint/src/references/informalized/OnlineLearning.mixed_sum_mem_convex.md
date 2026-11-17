<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.mixed_sum_mem_convex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of Mixed Averages

**Claim.** If $S\subseteq\mathbb R$ is convex, the weights of a mixed strategy are nonnegative and sum to one, and every $x_i$ lies in $S$, then the weighted average $\sum_i p_i x_i$ also lies in $S$.

**Proof.** Apply the finite convexity property of $S$ to the points $x_i$ with coefficients $p_i$. The coefficients are nonnegative and have total weight one, so their weighted average belongs to $S$.
