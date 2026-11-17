<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.exp_neg_three_halves_mul_density_le_shifted_density -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Gaussian density bound

**Claim.** For every real $t\ge1$, the standard Gaussian density satisfies $e^{-3/2}\varphi(t)\le\varphi(t+1/t)$.

**Proof.** The hypothesis implies $t>0$ and $1\le t^2$, hence $1/t^2\le1$. The standard Gaussian density is a positive constant times $\exp(-x^2/2)$. Expanding the shifted square gives $(t+1/t)^2=t^2+2+1/t^2$. Therefore $t^2+1/t^2\le t^2+1$, so the shifted exponential factor is at least $e^{-1}$ times the original one; in particular it is at least $e^{-3/2}$ times the original one. Multiplying by the positive normalizing constant proves the stated bound.
