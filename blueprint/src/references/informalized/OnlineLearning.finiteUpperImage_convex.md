<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.finiteUpperImage_convex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of the finite upper image

**Claim.** If $X$ is convex and each column payoff is convex in the row variable, then the finite upper image is convex.

**Proof.** Take two vectors $z,w$ in the finite upper image, witnessed by rows $x,x'\in X$, so $f(x,y)<z_y$ and $f(x',y)<w_y$ for every sampled column $y$. For convex weights $a,b$, the row $ax+bx'$ lies in $X$. Convexity of each column payoff gives $f(ax+bx',y)\le a f(x,y)+b f(x',y)$. The right-hand side is strictly less than $az_y+bw_y$ when both weights are positive. If one weight is zero, the other is one, and the corresponding original strict witness inequality gives the same conclusion. Thus the convex combination of $z,w$ is again in the finite upper image.
