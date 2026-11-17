<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.sampled_pureVsPayoff_le_concave_combo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concavity Bound for Sampled Payoffs

**Claim.** If the payoff section $y'\mapsto f(x_i,y')$ is concave on $Y$ and all sampled column points lie in $Y$, then the expected payoff of pure row $i$ against a mixed column strategy is at most the payoff at the mixed average of the column points.

**Proof.** Apply the finite Jensen inequality for a concave function, which bounds the weighted average of function values above by the function evaluated at the weighted average. Take the points to be $y_j$, the weights to be $q_j$, and the function to be $g(y')=f(x_i,y')$. Concavity and membership of every $y_j$ in $Y$ give $\sum_j q_j f(x_i,y_j)\leq f(x_i,\sum_j q_j y_j)$. The sum on the left is the expected payoff in the sampled game against the mixed column strategy.

**Key facts.** `OnlineLearning.concaveOn_le_mixed_sum`.
