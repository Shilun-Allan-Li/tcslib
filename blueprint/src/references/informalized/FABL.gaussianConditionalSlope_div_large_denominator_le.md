<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianConditionalSlope_div_large_denominator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Slope Denominator Comparison

**Claim.** For $\rho\in(0,1)$ and $t\ge 1$, let $s=(1-\rho)/\sqrt{1-\rho^2}$ be the Gaussian conditional slope. Then $\frac{s}{(1+s^2)t^2}\le\frac{s}{1+s^2t^2}$.

**Proof.** The slope $s$ is positive. Also $t>0$, so both denominators are positive and we may compare the fractions by cross-multiplication. Since $t\ge1$, we have $t^2\ge1$. The resulting inequality reduces to $s^2t^2\ge s^2$, which follows from $s^2\ge0$ and $t^2\ge1$.

**Key facts.** `FABL.gaussianConditionalSlope_pos`.
