<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.exp_neg_three_halves_mul_density_div_le_standardGaussian_interval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian interval probability lower bound

**Claim.** For every real $t\ge 1$, the standard Gaussian density at $t$, multiplied by $e^{-3/2}/t$, is at most the standard Gaussian probability of $(t,t+1/t)$.

**Proof.** Since $t\ge1$, we have $t>0$. The shifted density estimate gives $e^{-3/2}\varphi(t)\le\varphi(t+1/t)$ (by `exp_neg_three_halves_mul_density_le_shifted_density`). Dividing by the positive number $t$ preserves the inequality. The endpoint-density estimate then bounds $\varphi(t+1/t)/t$ above by the Gaussian probability of the interval, yielding the claim.

**Key facts.** `FABL.exp_neg_three_halves_mul_density_le_shifted_density`, `FABL.density_endpoint_div_le_standardGaussian_interval`.
