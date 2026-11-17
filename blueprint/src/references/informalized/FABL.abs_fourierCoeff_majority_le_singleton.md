<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLargestFourierCoefficient.lean :: FABL.abs_fourierCoeff_majority_le_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority coefficients bounded by singleton coefficients

**Claim.** For odd dimension $2m+1$, the absolute value of every Fourier coefficient of majority is at most its coefficient on any singleton coordinate.

**Proof.** If $|S|$ is even, the coefficient vanishes by the even-cardinality vanishing result (`fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card`), while a singleton coefficient equals the positive odd-majority influence (`fourierCoeff_majority_singleton_eq_oddMajorityInfluence`, `oddMajorityInfluence_pos`). Thus the claim holds. Otherwise write $|S|=2j+1$. If this odd size is at most the middle threshold $m+1$, apply the bound for odd-cardinality sets up to the middle (`abs_fourierCoeff_majority_le_singleton_of_odd_card_le_middle`). If it is larger, set $\ell=2(m-j)+1$ and choose a set $T$ of size $\ell$ in the full coordinate set. Then $|S|+|T|=(2m+1)+1$, so the complementary-set identity (`fourierCoeff_majority_complementary`) says the two coefficients differ by a sign; their absolute values are equal. The size $\ell$ is in the lower range, so the middle-range bound applied to $T$ proves the desired inequality for $S$.

**Key facts.** `FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card`, `FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence`, `FABL.oddMajorityInfluence_pos`, `FABL.abs_fourierCoeff_majority_le_singleton_of_odd_card_le_middle`, `FABL.fourierCoeff_majority_complementary`, `FABL.abs_fourierCoeff_majority_le_singleton_of_odd_card_le_middle`.
