<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.separating_functional_normalized_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Separator Payoff Bound

**Claim.** If the sum $W$ of the negated coordinate coefficients of the separator is positive, then every row's payoff averaged with the normalized weights is at least $c$.

**Proof.** Fix $x\in X$ and any $\delta>0$. The vector whose $y$-coordinate is $f(x,y)+\delta$ strictly exceeds the payoff vector of $x$ in every coordinate, so it belongs to the upper image. Separation therefore gives $L((f(x,y)+\delta)_y)<L(c\mathbf 1)$. Expand each functional value in the coordinate basis using the representation of a functional on a finite product as a sum of its coordinate values (`continuousLinearMap_pi_apply_eq_sum_single`). The identity $\sum_y L(e_y)=-W$ then turns this strict inequality into
\[
cW< -\sum_y f(x,y)L(e_y)+\delta W.
\]
Since $W>0$, the first term on the right is $W$ times the stated weighted payoff sum. Dividing by $W$ gives $c$ below that sum plus $\delta$. As this holds for every positive $\delta$, the sum is at least $c$.

**Key facts.** `OnlineLearning.continuousLinearMap_pi_apply_eq_sum_single`.
