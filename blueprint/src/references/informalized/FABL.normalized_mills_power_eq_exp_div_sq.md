<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.normalized_mills_power_eq_exp_div_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Gaussian Density Identity

**Claim.** For every $\rho\in(0,1)$ and every real $t>0$, the normalized power of the Gaussian density equals $\exp(-t^2/(1+\rho))/t^2$.

**Proof.** Set $a=2/(1+\rho)$ and $s=\sqrt{2\pi}$. The standard Gaussian density at $t$ is $s^{-1}\exp(-t^2/2)$. Because $s>0$ and $t>0$, real powers distribute over the positive factors, and the power of $s$ cancels the factor $s^a$ in front. The exponential factors combine to $\exp((-t^2/2)a)=\exp(-t^2/(1+\rho))$. The powers of $t$ in the denominator combine as $t^a t^{2-a}=t^2$, giving the claimed identity.
