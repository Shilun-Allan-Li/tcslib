<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.isConvexSet_signQuadrant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of a Sign Quadrant

**Claim.** For signs $s,t\in\{-1,1\}$, the set of $(x,y)\in\mathbb R^2$ satisfying $sx\ge0$ and $ty\ge0$ is convex.

**Proof.** Take two points $x,y$ in the set and nonnegative weights $\alpha,\beta$ with $\alpha+\beta=1$. In the first coordinate, the weighted combination satisfies $s(\alpha x_0+\beta y_0)=\alpha(sx_0)+\beta(sy_0)\ge0$, since each term on the right is nonnegative. The same argument gives $t(\alpha x_1+\beta y_1)=\alpha(tx_1)+\beta(ty_1)\ge0$. Thus every convex combination of two points in the set remains in the set, which proves convexity.
