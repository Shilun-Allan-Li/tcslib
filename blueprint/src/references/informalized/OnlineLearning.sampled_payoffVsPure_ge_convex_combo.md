<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.sampled_payoffVsPure_ge_convex_combo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity Bound for Sampled Payoffs

**Claim.** If the payoff section $x'\mapsto f(x',y_j)$ is convex on $X$ and all sampled row points lie in $X$, then its value at the mixed average of those points is at most the expected sampled payoff against column $j$.

**Proof.** Apply the finite Jensen inequality for a convex function: the value of a convex function at a weighted average is at most the weighted average of its values. Here the points are $x_i$, the weights are $p_i$, and the function is $g(x')=f(x',y_j)$. The hypotheses give convexity on $X$ and membership of every $x_i$ in $X$, while the mixed-strategy weights are nonnegative and sum to one. Thus $f(\sum_i p_i x_i,y_j)\leq\sum_i p_i f(x_i,y_j)$. By the definition of the sampled game, the right-hand side is its expected payoff against column $j$.

**Key facts.** `OnlineLearning.convexOn_mixed_sum_le`.
