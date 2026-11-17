<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseDuality.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_identities -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Noise Identities

**Claim.** For weights summing to one, the weighted square of the noisy version of $g$ equals its stated second-moment expression, and the mixed weighted product of the noisy versions of $f$ and $g$ is symmetric in which function is expanded.

**Proof.** Expand each summand algebraically. In the first identity, the three terms are the weighted second moment of $g$, the cross term proportional to $\sum_i w_i g_i=m_g$, and the constant term proportional to $\sum_i w_i=1$. This gives $\rho^2\sum_iw_i g_i^2+2\rho(1-\rho)m_g^2+(1-\rho)^2m_g^2$, whose last two coefficients combine to $1-\rho^2$. For the second identity, expansion of the left side gives $\rho\sum_iw_if_ig_i+(1-\rho)m_fm_g$. Expanding the right side gives the same expression, with the two scalar factors $m_f,m_g$ interchanged; they commute.
