<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.separating_coordinate_nonpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonpositive Separating Coordinates

**Claim.** If a continuous linear functional strictly separates the finite upper image from a fixed vector, then its value on each standard basis vector is nonpositive.

**Proof.** Fix a coordinate $y$ and suppose, for contradiction, that $L(e_y)>0$, where $e_y$ is the standard basis vector. The finite upper image is nonempty, so choose a point $z$ in it. Strict separation gives $L(z)<L(c)$, hence $L(c)-L(z)+1>0$. Set $t=(L(c)-L(z)+1)/L(e_y)$, which is nonnegative. Increasing only the $y$-coordinate of $z$ by $t$ leaves the point in the finite upper image: the defining strict coordinate inequalities are preserved, using that $t\geq0$ at coordinate $y$ and that other coordinates are unchanged. This upward-closure fact is `finiteUpperImage_upper`. By linearity, the shifted point has functional value $L(z)+tL(e_y)=L(c)+1$, contradicting the strict separation inequality at that point. Therefore $L(e_y)\leq0$.

**Key facts.** `OnlineLearning.finiteUpperImage_nonempty`, `OnlineLearning.finiteUpperImage_upper`.
