<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productResamplingNoiseSensitivity_le_sqrt_two_full -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square-root bound including zero noise

**Claim.** For every $\delta\in[0,1]$, the product resampling noise sensitivity of a product linear threshold function is at most $\sqrt2\,\sqrt\delta$.

**Proof.** If $\delta=0$, the zero-noise identity (`productResamplingNoiseSensitivity_zero`) says the sensitivity is zero, which is the desired bound. Otherwise, the interval hypothesis gives $0<\delta\le1$, so apply `productResamplingNoiseSensitivity_le_sqrt_two` to obtain the claimed estimate.

**Key facts.** `FABL.productResamplingNoiseSensitivity_zero`, `FABL.productResamplingNoiseSensitivity_le_sqrt_two`.
