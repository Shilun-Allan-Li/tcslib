<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.totalInfluence_composedMajority_isTheta_sqrt_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic influence growth

**Claim.** As $m$ tends to infinity, the total influence of the composed majority function is bounded above and below by positive constant multiples of $\sqrt{2m+3}$ for all sufficiently large $m$.

**Proof.** By the pointwise upper and lower estimates, the total influence is nonnegative and satisfies $\frac18\sqrt{2m+3}\le I_m\le 2\sqrt{2m+3}$ for every $m$, where $I_m$ denotes the total influence of the composed majority function. These two uniform inequalities give the required two-sided asymptotic bound, hence the claimed order of growth.

**Key facts.** `FABL.totalInfluence_nonneg`, `FABL.totalInfluence_composedMajority_upper`, `FABL.totalInfluence_composedMajority_lower`.
