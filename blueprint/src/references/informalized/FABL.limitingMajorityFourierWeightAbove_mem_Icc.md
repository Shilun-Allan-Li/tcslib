<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightAbove_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-level tail bounds

**Claim.** If $k$ is odd, the limiting majority Fourier weight above $k$ lies between $M(k)(1-1/k)$ and $M(k)(1+1/(3k))$, where $M(k)=(2/\pi)^{3/2}k^{-1/2}$.

**Proof.** The power bounds for the tail give a lower bound of $(2/\pi)^{3/2}(k+2)^{-1/2}$ and an upper bound of $(2/\pi)^{3/2}\bigl(k^{-1/2}+(1/3)k^{-3/2}\bigr)$. Since the constant $(2/\pi)^{3/2}$ is nonnegative, the inequality $(k^{-1/2})(1-1/k)\leq(k+2)^{-1/2}$ for odd $k$ yields the claimed lower endpoint. For the upper endpoint, use $k^{-3/2}=k^{-1/2}/k$; factoring out $(2/\pi)^{3/2}k^{-1/2}$ gives exactly $M(k)(1+1/(3k))$.

**Key facts.** `FABL.limitingMajorityFourierWeightAbove_power_bounds`, `FABL.odd_rpow_neg_half_mul_one_sub_inv_le_succ`, `FABL.odd_rpow_neg_three_halves_eq_neg_half_div`.
