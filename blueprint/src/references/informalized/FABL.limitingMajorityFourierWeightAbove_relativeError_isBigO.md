<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightAbove_relativeError_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relative tail error estimate

**Claim.** Along odd natural numbers tending to infinity, $T(k)/M(k)-1=O(1/k)$, where $T(k)$ is the tail weight and $M(k)=(2/\pi)^{3/2}k^{-1/2}$.

**Proof.** For each odd $k$, the absolute value of the relative error is bounded by $1/k$ (FABL.abs_limitingMajorityFourierWeightAbove_div_tailMain_sub_one_le). The comparison function $1/k$ is positive on odd $k$, since every odd natural number is positive. This pointwise norm bound is precisely the criterion for the stated big-O estimate along the odd naturals.

**Key facts.** `FABL.abs_limitingMajorityFourierWeightAbove_div_tailMain_sub_one_le`.
