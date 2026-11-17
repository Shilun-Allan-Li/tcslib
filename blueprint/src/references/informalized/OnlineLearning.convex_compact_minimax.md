<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimax.lean :: OnlineLearning.convex_compact_minimax -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convex-Concave Minimax Equality

**Claim.** Under the stated compactness, convexity, continuity, semicontinuity, and quasi-convexity and quasi-concavity assumptions, the minimum over $X$ of the supremum over $Y$ equals the supremum over $Y$ of the minimum over $X$.

**Proof.** The proof invokes the separation-based minimax theorem, which reduces the equality to a finite-intersection condition for sublevel sets. The finite-intersection criterion says that if, for every positive $\varepsilon$ and every finite collection of points of $Y$, there is a point of $X$ whose payoff at each selected point is at most the candidate value $\sup_{y\in Y}\inf_{x\in X}f(x,y)+\varepsilon$, then the minimax equality follows. The separation argument supplies exactly this condition. Applying the criterion therefore proves the equality.

**Key facts.** `OnlineLearning.convex_compact_minimax_by_separation`.
