<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantAtThreshold_lower_mills -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mills-Type Gaussian Quadrant Bound

**Claim.** For $0<\rho<1$ and $t\ge1$, the Gaussian quadrant probability is at least the product of a lower bound for the standard Gaussian mass of $(t,t+1/t)$ and a lower bound for the upper tail at $s_\rho t$.

**Proof.** Since $t\ge1$, it is positive; and $s_\rho>0$ (\texttt{gaussianConditionalSlope\_pos}), so $s_\rho t>0$. The interval estimate gives $e^{-3/2}\phi(t)/t\le\mathbb P(t<Z<t+1/t)$, where $\phi$ is the standard Gaussian density (\texttt{exp\_neg\_three\_halves\_mul\_density\_div\_le\_standardGaussian\_interval}). The lower Mills estimate also gives $x\phi(x)/(1+x^2)\le\mathbb P(Z>x)$ for positive $x$; apply it at $x=s_\rho t$ (\texttt{density\_mul\_t\_div\_one\_add\_sq\_le\_standardGaussianUpperTail}). Multiplying these nonnegative inequalities bounds the product of the interval mass and the tail at $s_\rho t$ from below by the displayed density expression. The rectangle lower bound then places this product below the Gaussian quadrant probability (\texttt{gaussianQuadrantAtThreshold\_ge\_rectangle}).

**Key facts.** `FABL.gaussianConditionalSlope_pos`, `FABL.exp_neg_three_halves_mul_density_div_le_standardGaussian_interval`, `FABL.density_mul_t_div_one_add_sq_le_standardGaussianUpperTail`, `FABL.gaussianQuadrantAtThreshold_ge_rectangle`.
