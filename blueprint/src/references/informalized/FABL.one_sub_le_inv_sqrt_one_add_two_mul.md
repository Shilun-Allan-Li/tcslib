<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.one_sub_le_inv_sqrt_one_add_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal square-root inequality

**Claim.** For every $\epsilon\in[0,1]$, $1-\epsilon\le 1/\sqrt{1+2\epsilon}$.

**Proof.** Because $\epsilon\ge 0$, the quantity $1+2\epsilon$ is positive, so its square root is positive. Multiplying the desired inequality by this positive square root reduces it to $(1-\epsilon)\sqrt{1+2\epsilon}\le 1$. Both sides are nonnegative: the left because $\epsilon\le1$, and the right trivially. Thus it suffices to compare their squares. The difference between the square of the right side and that of the left is
\[
1-(1-\epsilon)^2(1+2\epsilon)=\epsilon^2(3-2\epsilon),
\]
which is nonnegative since $\epsilon^2\ge0$ and $3-2\epsilon\ge1$ on the given interval. This proves the inequality.
