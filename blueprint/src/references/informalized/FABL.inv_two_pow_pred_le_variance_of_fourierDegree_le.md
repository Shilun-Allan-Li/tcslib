<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/JuntaStableInfluence.lean :: FABL.inv_two_pow_pred_le_variance_of_fourierDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance from Fourier Degree

**Claim.** If a Boolean function is nonconstant and its real-valued sign embedding has Fourier degree at most the positive integer $k$, then its variance under the uniform distribution is at least $2^{-(k-1)}$.

**Proof.** Apply the distance-from-a-constant bound to the two possible constant signs, $1$ and $-1$. Nonconstancy ensures the function is not equal to either constant, so its relative Hamming distance from each is at least $2^{-k}$. The distance to the nearest constant is the minimum of these two distances, hence is also at least $2^{-k}$. The lower variance estimate in `variance_bounds_distanceToNearestConstant` says that the variance is at least twice the distance to the nearest constant; consequently it is at least $2\cdot 2^{-k}$. Since $k>0$, the exponent identity $2^{-(k-1)}=2\cdot 2^{-k}$ gives the stated bound.

**Key facts.** `FABL.inv_two_pow_le_relativeHammingDist_const_of_fourierDegree_le`, `FABL.variance_bounds_distanceToNearestConstant`.
