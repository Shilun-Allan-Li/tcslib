<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianBadTailProbability_hasSoftPower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian bad-tail soft power

**Claim.** For every $\rho\in(0,1)$, as $\mu\to0$ through $(0,1)$, the logarithmic ratio of the Gaussian bad-tail probability to $\log\mu$ tends to $1/\rho^2$.

**Proof.** The logarithmic ratio at threshold $t$ tends to $1/\rho^2$ as $t\to\infty$ by the stated tail-logarithm limit (`tendsto_log_gaussianBadTail_div_tailLog`). The upper quantile tends to infinity as $\mu\to0$ (`tendsto_standardGaussianUpperQuantile_atBot`), so composing these limits gives the same limit with $t$ equal to the quantile. To identify the denominator after composition, use the quantile identity: the standard Gaussian upper tail at the upper quantile of $\mu$ is exactly $\mu$ (`standardGaussianUpperTail_quantile`). The resulting expression is therefore the logarithm of the Gaussian bad-tail probability divided by $\log\mu$, as required.

**Key facts.** `FABL.tendsto_log_gaussianBadTail_div_tailLog`, `FABL.tendsto_standardGaussianUpperQuantile_atBot`, `FABL.standardGaussianUpperTail_quantile`.
