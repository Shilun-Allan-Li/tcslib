<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.convex_compact_minimax_of_finite_sublevel_intersections -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimax equality from finite intersections

**Claim.** Under the stated compactness, convexity, continuity, boundedness, and finite-sublevel-intersection assumptions, the upper value equals the lower value.

**Proof.** Write $v=\sup_{y\in Y}\inf_{x\in X}f(x,y)$. For any $\varepsilon>0$, the finite-intersection hypothesis gives a row point $x\in X$ such that $f(x,y)\le v+\varepsilon$ for every column $y$. Hence $\sup_{y\in Y}f(x,y)\le v+\varepsilon$, and taking the infimum over rows shows that the upper value is at most $v+\varepsilon$. Since this holds for every positive $\varepsilon$, the upper value is at most $v$. The reverse inequality is weak minimax: for each row and column, the column's infimum over rows is no larger than that row's supremum over columns; taking the supremum over columns and then the infimum over rows gives $v\le\inf_{x\in X}\sup_{y\in Y}f(x,y)$. Together these inequalities give equality.

**Key facts.** `OnlineLearning.exists_forall_le_of_finite_sublevel_intersections`, `OnlineLearning.weak_convex_compact_minimax`.
