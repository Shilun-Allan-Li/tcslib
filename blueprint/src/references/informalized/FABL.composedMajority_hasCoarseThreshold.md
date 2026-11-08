<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.composedMajority_hasCoarseThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coarse Threshold for Composed Majority

**Claim.** For every $0<\epsilon<1/4$, the composed-majority family with dimension $2+(2k+1)$ has a coarse threshold: its normalized threshold-width sequence does not converge to zero.

**Proof.** The cited result states directly that, for this $\epsilon$, the normalized threshold-width sequence for the composed-majority family does not tend to zero (`composedMajority_normalizedThresholdWidth_not_tendsto_zero`). By definition, having a coarse threshold is precisely the negation of this convergence to zero. The hypotheses and family in the stated conclusion match those in that result, with $\epsilon$ viewed in $(0,1/2)$ as ensured by `epsilon_mem_Ioo_half_of_mem_Ioo_quarter`.

**Key facts.** `FABL.composedMajority_normalizedThresholdWidth_not_tendsto_zero`, `FABL.epsilon_mem_Ioo_half_of_mem_Ioo_quarter`.
