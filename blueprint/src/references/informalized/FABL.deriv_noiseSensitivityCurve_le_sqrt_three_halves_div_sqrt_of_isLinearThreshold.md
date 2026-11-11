<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LTFNoiseSensitivityDerivative.lean :: FABL.deriv_noiseSensitivityCurve_le_sqrt_three_halves_div_sqrt_of_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise-sensitivity derivative bound

**Claim.** For a linear threshold function and $0<\delta\le 1/2$, the derivative of its noise-sensitivity curve is at most $\sqrt{3/2}/\sqrt{\delta}$.

**Proof.** The derivative of the noise-sensitivity curve is the total stable influence at parameter $1-2\delta$ (`hasDerivAt_noiseSensitivityCurve`). The weighted influence inequality (`delta_mul_totalStableInfluence_le_noiseSensitivity`) bounds $\delta$ times this derivative by the noise sensitivity at $\delta$. The linear-threshold noise-sensitivity bound (`peresNoiseSensitivityBound`) then bounds that quantity by $\sqrt{3/2}\sqrt{\delta}$. Since $\delta>0$, its square root is positive, and dividing by $\sqrt{\delta}$ gives the claimed estimate.

**Key facts.** `FABL.hasDerivAt_noiseSensitivityCurve`, `FABL.delta_mul_totalStableInfluence_le_noiseSensitivity`, `FABL.peresNoiseSensitivityBound`.
