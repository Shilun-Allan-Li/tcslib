<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.finiteUpperImage_upper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upward Closure of the Finite Upper Image

**Claim.** If a vector belongs to the finite upper image and another vector is at least as large in every coordinate, then the latter also belongs to the finite upper image.

**Proof.** Membership supplies a row point $x\in X$ whose payoff is strictly below each coordinate of $z$. For every sampled column $y$, the inequalities $f(x,y)<z_y\le z'_y$ imply $f(x,y)<z'_y$. The same $x$ therefore witnesses that $z'$ belongs to the finite upper image.
