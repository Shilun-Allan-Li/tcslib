<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.normalizedThresholdWidth_composedMajority_eq_thresholdWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Majority Width Normalization

**Claim.** For every $\epsilon\in(0,1/2)$ and natural number $m$, the normalized threshold width of the composed-majority family at index $m$ equals the threshold width of composed majority on $2+(2m+1)$ inputs, with both widths taken at $\epsilon$.

**Proof.** Unfolding the normalized width identifies it as the threshold width of the $m$th family member divided by the bias variance scale at that member’s critical probability. The family member is composed majority, whose critical probability is $1/2$ by the critical-probability theorem (`criticalProbability_composedMajority`). Since $4(1/2)(1-1/2)=1$, the normalization factor is $1$. The family definition and its arity reduce the remaining expression to the stated threshold width.

**Key facts.** `FABL.criticalProbability_composedMajority`.
