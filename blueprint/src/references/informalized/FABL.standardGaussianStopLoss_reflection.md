<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.standardGaussianStopLoss_reflection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflection identity for Gaussian stop loss

**Claim.** For every real $t$, the standard Gaussian stop-loss function at $t$ equals $-t$ plus its value at $-t$.

**Proof.** Apply the stop-loss identity at $t$ and at $-t$. The standard Gaussian density is even, so the density terms agree; the upper-tail probabilities at opposite arguments sum to one. Substituting these relations into the two stop-loss formulas and simplifying gives $\mathbb{E}(Z-t)^+=-t+\mathbb{E}(Z+t)^+$.

**Key facts.** `FABL.standardGaussianStopLoss_eq`, `FABL.gaussianPDFReal_zero_one_neg`, `FABL.standardGaussianUpperTail_neg`.
