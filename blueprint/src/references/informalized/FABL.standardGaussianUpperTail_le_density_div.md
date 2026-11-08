<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianMillsRatio.lean :: FABL.standardGaussianUpperTail_le_density_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail Bound by Density over Threshold

**Claim.** For every $t>0$, the standard Gaussian upper-tail probability at $t$ is at most the standard Gaussian density at $t$ divided by $t$.

**Proof.** Consider the stop-loss integral, whose integrand is the positive part of $z-t$. This integrand is nonnegative everywhere, so the stop-loss integral is nonnegative. The stop-loss identity expresses it as the density at $t$ minus $t$ times the upper-tail probability (`standardGaussianStopLoss_eq`). Thus $t$ times the tail is at most the density. Since $t>0$, division by $t$ preserves the inequality and gives the result.

**Key facts.** `FABL.standardGaussianStopLoss_eq`.
