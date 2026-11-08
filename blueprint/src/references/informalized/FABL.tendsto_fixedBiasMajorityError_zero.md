<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.tendsto_fixedBiasMajorityError_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decay of Fixed-Bias Majority Error

**Claim.** For every real $d>0$, the sequence $2\exp(-4d^2m)$ tends to zero as $m\to\infty$.

**Proof.** Because $d>0$, the coefficient $-4d^2$ is negative. Hence $(-4d^2)m$ tends to $-\infty$ as $m\to\infty$. The exponential therefore tends to zero; multiplying by $2$ preserves that limit. The defined error sequence is exactly this expression, so it too tends to zero.
