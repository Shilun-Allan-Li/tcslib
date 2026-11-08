<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productResamplingNoiseSensitivity_le_sqrt_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform square-root bound

**Claim.** For a product linear threshold function and $0<\delta\le1$, its product resampling noise sensitivity is at most $\sqrt{2}\,\sqrt{\delta}$.

**Proof.** Split into two ranges. If $\delta\le 1/2$, the Peres bound gives $\sqrt{3/2}\,\sqrt{\delta}$; since $\sqrt{3/2}\le\sqrt2$ and $\sqrt\delta\ge0$, this implies the desired estimate. If $\delta>1/2$, any disagreement probability is at most $1$ (`pmfDisagreementProbability_le_one`). Meanwhile $2\delta>1$, so $1=\sqrt1\le\sqrt{2\delta}=\sqrt2\,\sqrt\delta$. Combining these inequalities proves the result.

**Key facts.** `FABL.productResamplingNoiseSensitivity_le_peres`, `FABL.pmfDisagreementProbability_le_one`.
