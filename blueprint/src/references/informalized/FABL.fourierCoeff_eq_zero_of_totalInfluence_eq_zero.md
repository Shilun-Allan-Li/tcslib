<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.fourierCoeff_eq_zero_of_totalInfluence_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing from Zero Total Influence

**Claim.** If the total influence of a real-valued function is zero, then every nonempty coordinate set has Fourier coefficient zero.

**Proof.** The total influence equals the sum over all coordinate sets $T$ of $|T|\widehat f(T)^2$ (`totalInfluence_eq_sum_card_mul_sq_fourierCoeff`). Under the hypothesis this sum is zero. Each term is nonnegative, so the term for the given nonempty $S$ must itself vanish: $|S|\widehat f(S)^2=0$. Since $S$ is nonempty, $|S|>0$, and therefore its squared coefficient is zero. Hence the coefficient is zero.

**Key facts.** `FABL.totalInfluence_eq_sum_card_mul_sq_fourierCoeff`.
