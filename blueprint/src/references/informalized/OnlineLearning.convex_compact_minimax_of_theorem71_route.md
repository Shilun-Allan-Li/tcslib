<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.convex_compact_minimax_of_theorem71_route -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimax equality from finite row samples

**Claim.** Under the stated hypotheses, the finite-sample no-regret bound and finite-sample approximation property imply minimax equality.

**Proof.** Write $v=\sup_{y\in Y}\inf_{x\in X}f(x,y)$. Given any $\varepsilon>0$, choose a nonempty finite row sample $u$ whose finite-sample lower value is at most $v+\varepsilon$. The assumed finite no-regret bound says that the upper value is at most this finite-sample lower value, so it is at most $v+\varepsilon$. Letting $\varepsilon$ decrease to zero gives that the upper value is at most $v$. In the other direction, weak minimax gives $v\le\inf_{x\in X}\sup_{y\in Y}f(x,y)$. Thus the two values agree.

**Key facts.** `OnlineLearning.weak_convex_compact_minimax`.
