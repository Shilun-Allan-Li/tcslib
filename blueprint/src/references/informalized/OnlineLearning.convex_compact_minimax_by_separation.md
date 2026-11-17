<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.convex_compact_minimax_by_separation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convex-Concave Minimax Equality by Separation

**Claim.** For nonempty convex sets $X,Y\subseteq\mathbb{R}$ with $X$ compact, a payoff bounded above and below on $X\times Y$, continuous and convex in the $X$ variable, and concave in the $Y$ variable, the minimax equality holds.

**Proof.** First, a finite-intersection criterion reduces the minimax equality to showing that for every positive $\varepsilon$ and every finite collection of column points, there is a row point whose payoff at all those columns is at most $\sup_{y\in Y}\inf_{x\in X}f(x,y)+\varepsilon$. The proof obtains this finite-sublevel-set condition by separation. Applying the criterion then yields the claimed equality.

**Key facts.** `OnlineLearning.convex_compact_minimax_of_finite_sublevel_intersections`, `OnlineLearning.finite_sublevel_intersections_by_separation`.
