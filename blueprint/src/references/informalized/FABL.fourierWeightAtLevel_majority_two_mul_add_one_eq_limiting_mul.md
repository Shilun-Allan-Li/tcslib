<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.fourierWeightAtLevel_majority_two_mul_add_one_eq_limiting_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact majority Fourier weight

**Claim.** For $j\le m$, the level-$(2j+1)$ Fourier weight of majority on the sign cube of dimension $2m+1$ equals the stated limiting majority weight times $\frac{\pi}{2}(2m+1)I_{m-j}I_m$.

**Proof.** Choose a subset $S$ of the $2m+1$ coordinates with $|S|=2j+1$. The level-weight symmetry formula says the total weight is $\binom{2m+1}{2j+1}$ times the squared Fourier coefficient on this one subset (`fourierWeightAtLevel_majority_eq_choose_mul`). The odd-level coefficient formula (`fourierCoeff_majority_two_mul_add_one`) expresses that coefficient using $(-1)^j\binom mj/\binom{2m}{2j}$ times $I_m$. Squaring removes the sign. The binomial identity $(2m+1)\binom{2m}{2j}=(2j+1)\binom{2m+1}{2j+1}$ converts the resulting binomial ratio to $(2m+1)/(2j+1)$. Next, the majority binomial factorization (`majority_binomial_factorization`) rewrites the remaining factor $\binom mj^2\binom{2m}{m}/\binom{2m}{2j}$ as $\binom{2j}{j}\binom{2(m-j)}{m-j}$. Since $2^{2j}2^{2(m-j)}=2^{2m}$, the normalized factors separate as $I_jI_{m-j}$, leaving $\frac{2m+1}{2j+1}I_jI_{m-j}I_m$. Finally, the formula for the limiting majority weight (`limitingMajorityFourierWeight_eq`), specialized to the odd index $2j+1$, identifies its coefficient with $\frac{4}{\pi(2j+1)2^{2j+1}}\binom{2j}{j}$. Rearranging gives the claimed expression.

**Key facts.** `FABL.fourierWeightAtLevel_majority_eq_choose_mul`, `FABL.fourierCoeff_majority_two_mul_add_one`, `FABL.majority_binomial_factorization`, `FABL.limitingMajorityFourierWeight_eq`.
