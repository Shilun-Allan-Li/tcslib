<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.two_mul_variance_le_totalInfluence_of_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance bounded by total influence

**Claim.** If \(f\) is even on the sign cube, then twice its variance is at most its total influence.

**Proof.** Use the Fourier formulas expressing variance as the sum of squared Fourier coefficients over nonempty sets and total influence as the sum of each squared coefficient weighted by the set's size (\(\texttt{FABL.variance_eq_sum_sq_fourierCoeff}\), \(\texttt{FABL.totalInfluence_eq_sum_card_mul_sq_fourierCoeff}\)). Compare the summands set by set. The empty set contributes zero to the variance sum. For a nonempty set of even size, its size is at least two, so its contribution to total influence is at least twice its squared coefficient. For a set of odd size, evenness of \(f\) forces its Fourier coefficient to vanish (\(\texttt{FABL.fourierCoeff_eq_zero_of_even_of_odd_card}\)), so it contributes zero on both sides. Summing these comparisons proves the result.

**Key facts.** `FABL.variance_eq_sum_sq_fourierCoeff`, `FABL.totalInfluence_eq_sum_card_mul_sq_fourierCoeff`, `FABL.fourierCoeff_eq_zero_of_even_of_odd_card`.
