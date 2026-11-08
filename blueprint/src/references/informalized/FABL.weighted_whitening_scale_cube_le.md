<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.weighted_whitening_scale_cube_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Cube Scale Bound

**Claim.** For $-1<\rho<1$ and $c\in\mathbb R$, the weighted sum of the two cubed scales is at most $4|c|^3/\sqrt{1-\rho^2}$.

**Proof.** The hypotheses give $1+\rho>0$, $1-\rho>0$, and hence $1-\rho^2=(1+\rho)(1-\rho)>0$. Thus all three square roots involved are positive, and $\sqrt{1-\rho^2}=\sqrt{1+\rho}\sqrt{1-\rho}$. Since $\sqrt{2}^2=2$ and $\sqrt{1\pm\rho}^{\,2}=1\pm\rho$, expanding each cube and canceling the positive factors shows that its weighted term simplifies to $\sqrt{2}|c|^3/\sqrt{1+\rho}$ or $\sqrt{2}|c|^3/\sqrt{1-\rho}$, respectively. Next, $\sqrt{2}\sqrt{1-\rho}\le 2$ follows by squaring nonnegative quantities and using $\rho>-1$; likewise $\sqrt{2}\sqrt{1+\rho}\le 2$ follows from $\rho<1$. Dividing these inequalities by the positive product $\sqrt{1+\rho}\sqrt{1-\rho}$ yields $\sqrt{2}/\sqrt{1+\rho}\le 2/\sqrt{1-\rho^2}$ and $\sqrt{2}/\sqrt{1-\rho}\le 2/\sqrt{1-\rho^2}$. Multiply both inequalities by the nonnegative $|c|^3$ and add them. The resulting right side is $4|c|^3/\sqrt{1-\rho^2}$, as required.
