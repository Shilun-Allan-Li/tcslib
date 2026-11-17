<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightError_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic error in majority Fourier weight

**Claim.** As odd integers $k$ tend to infinity, the error between the limiting majority Fourier weight and $(2/\pi)^{3/2}k^{-3/2}$ is $O\bigl((2/\pi)^{3/2}k^{-5/2}\bigr)$.

**Proof.** For each odd $k$, the error lies between zero and the main level divided by $k$ (FABL.limitingMajorityFourierWeightError_mem_Icc). Consequently its absolute value is bounded by that quotient. The main level is positive for positive $k$ (FABL.majorityFourierLevelMain_pos), and odd $k$ is positive, so the comparison function is nonnegative. The pointwise bound therefore gives the claimed big-O estimate along the odd naturals.

**Key facts.** `FABL.limitingMajorityFourierWeightError_mem_Icc`, `FABL.majorityFourierLevelMain_pos`.
