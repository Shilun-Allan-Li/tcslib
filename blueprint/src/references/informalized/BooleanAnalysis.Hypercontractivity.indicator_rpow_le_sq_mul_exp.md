<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/Influence.lean :: BooleanAnalysis.Hypercontractivity.indicator_rpow_le_sq_mul_exp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Power and Exponential Estimate

**Claim.** If $0<\alpha\le1$ and $\rho\ge0$, then $\alpha^{2/(1+\rho)}\le\alpha^2\exp(2\rho\log(1/\alpha))$.

**Proof.** Because $1+\rho>0$ and $\rho^2\ge0$, we have $2(1-\rho)\le2/(1+\rho)$. For a base $\alpha$ between zero and one, increasing the exponent weakly decreases its real power. Thus $\alpha^{2/(1+\rho)}\le\alpha^{2(1-\rho)}$. Finally, the real-power and logarithm identities rewrite the latter as $\alpha^2\exp(2\rho\log(1/\alpha))$.
