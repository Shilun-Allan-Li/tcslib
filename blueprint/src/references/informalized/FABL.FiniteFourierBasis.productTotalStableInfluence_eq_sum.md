<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.productTotalStableInfluence_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Stable Influence Fourier Sum

**Claim.** For $0<\rho\le 1$, total stable influence equals the sum over multi-indices of their support size times $\rho^{|S|-1}$ times the squared Fourier coefficient.

**Proof.** Expand total stable influence as the sum of the coordinate stable influences, and replace each coordinate term by its stable-influence polynomial (`productStableInfluence_eq_polynomial`). Interchange the finite sums so the terms are grouped by multi-index. For each fixed multi-index, its support size is the sum over coordinates of the indicator that the index is nonconstant there (`multiIndexOrder_cast_eq_sum_indicator`). Thus each squared Fourier coefficient receives one copy of its weight for every coordinate in its support, hence exactly $|S|$ copies. Collecting these contributions gives the stated sum.

**Key facts.** `FABL.FiniteFourierBasis.productStableInfluence_eq_polynomial`, `FABL.multiIndexOrder_cast_eq_sum_indicator`.

**Caveat.** The supplied informal statement also states a derivative identity for stability. The formal theorem and proof establish the displayed total stable-influence Fourier sum.
