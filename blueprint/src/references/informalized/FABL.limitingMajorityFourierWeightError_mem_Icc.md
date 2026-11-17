<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on the limiting weight error

**Claim.** For every odd natural number $k$, the error between the limiting majority Fourier weight and $(2/\pi)^{3/2}k^{-3/2}$ lies between zero and $(2/\pi)^{3/2}k^{-5/2}$.

**Proof.** Write $k=2j+1$ and let $N=2j+1$. The limiting weight at this odd level equals $2/(\pi N)$ times the odd majority influence, and its main approximation equals the same positive factor times the main influence (FABL.limitingMajorityFourierWeight_two_mul_add_one_eq; FABL.majorityFourierLevelMain_two_mul_add_one_eq). Subtracting these identities shows that the weight error is $2/(\pi N)$ times the influence error. The latter lies between zero and the main influence divided by $N$ (FABL.oddMajorityInfluenceError_mem_Icc). Multiplication by the nonnegative factor preserves both inequalities, giving an upper bound of the main level divided by $N$. Since $N=k$, this is the stated $(2/\pi)^{3/2}k^{-5/2}$ bound.

**Key facts.** `FABL.limitingMajorityFourierWeight_two_mul_add_one_eq`, `FABL.majorityFourierLevelMain_two_mul_add_one_eq`, `FABL.oddMajorityInfluenceError_mem_Icc`.
