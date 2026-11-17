<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.composedMajority_normalizedThresholdWidth_not_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Width Does Not Vanish

**Claim.** For $0<\epsilon<1/4$, the normalized threshold-width sequence of the composed-majority family does not converge to zero.

**Proof.** Set $a=1/2-\sqrt{\epsilon}$. The square-root bound from $\epsilon<1/4$ gives $a>0$. The eventual lower-bound result says that the normalized widths are eventually strictly greater than $a$ (`eventually_composedMajority_normalizedThresholdWidth_gt`). If they converged to zero, convergence would make them eventually less than $a/2$. The two eventual statements hold simultaneously for some index, which would force that width to be both greater than $a$ and less than $a/2$, an impossibility. Hence the sequence does not converge to zero.

**Key facts.** `FABL.eventually_composedMajority_normalizedThresholdWidth_gt`.
