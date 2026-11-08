<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLargestFourierCoefficient.lean :: FABL.abs_fourierCoeff_majority_le_singleton_of_odd_card_le_middle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority coefficients decrease through the middle

**Claim.** For a set $S$ of size $2j+1$ with $2j+1\leq m+1$ in dimension $2m+1$, its majority Fourier coefficient in absolute value is at most the coefficient on any singleton.

**Proof.** Proceed by induction on $j$, with the set $S$ allowed to vary. At $j=0$, the set has size one; the coefficient formula for odd-cardinality sets (`abs_fourierCoeff_majority_two_mul_add_one`) reduces its absolute value to the singleton coefficient, using the identity between singleton coefficients and odd-majority influence (`fourierCoeff_majority_singleton_eq_oddMajorityInfluence`). For the induction step, choose a set $T$ of size $2j+1$ from the full coordinate set. The successive-odd-level identity (`abs_fourierCoeff_majority_next_odd_eq`) expresses the absolute coefficient at size $2(j+1)+1$ as the coefficient at size $2j+1$ multiplied by $(2j+1)/(2m-2j-1)$. The middle-size assumption ensures the denominator is positive and this ratio is at most one. Since an absolute value is nonnegative, multiplication by this factor cannot increase it; the induction hypothesis bounds the coefficient for $T$ by the singleton coefficient, proving the step.

**Key facts.** `FABL.abs_fourierCoeff_majority_two_mul_add_one`, `FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence`, `FABL.abs_fourierCoeff_majority_next_odd_eq`.
