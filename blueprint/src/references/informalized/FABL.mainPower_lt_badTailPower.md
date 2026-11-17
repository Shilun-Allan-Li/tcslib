<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.mainPower_lt_badTailPower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison of two powers

**Claim.** For every $\rho$ with $0<\rho<1$, one has $\frac{2}{1+\rho}<\frac{1}{\rho^2}$.

**Proof.** The hypotheses imply $1-\rho>0$, $1+2\rho>0$, and $1+\rho>0$. Because the denominators $1+\rho$ and $\rho^2$ are positive, cross multiplication reduces the desired inequality to $2\rho^2<1+\rho$. The difference of the right and left sides factors as $(1-\rho)(1+2\rho)$, which is positive, proving the strict inequality.
