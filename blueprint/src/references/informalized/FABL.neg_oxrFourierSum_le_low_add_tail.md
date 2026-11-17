<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.neg_oxrFourierSum_le_low_add_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Fourier sum bound

**Claim.** Under the stated assumptions, the negative signed Fourier sum is at most the square root tail term plus the low-degree sum of squared Fourier coefficients times their absolute random-subset averages.

**Proof.** Set $b=\sqrt{(1-\delta)^t}$, which is nonnegative. For each subset $S$, the negative of its signed summand is at most $\widehat f(S)^2$ times the corresponding absolute average: this follows from the bound of a negative average by the average of absolute values (`FABL.neg_oxrRandomSubsetFourierAverage_le_abs`), multiplied by the nonnegative square $\widehat f(S)^2$. If $|S|\leq t$, add the nonnegative quantity $b\widehat f(S)^2$ to this bound. If $|S|>t$, the absolute average is at most $b$ (`FABL.oxrRandomSubsetAbsFourierAverage_le_sqrt_of_lt_card`), so the negative summand is at most $b\widehat f(S)^2$. These two cases bound each summand by the low-degree absolute-average contribution, when applicable, plus $b\widehat f(S)^2$. Summing separates the low-degree part from $b\sum_S\widehat f(S)^2$. The squared Fourier coefficients sum to at most one (`FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`), so this last term is at most $b$, as required.

**Key facts.** `FABL.neg_oxrRandomSubsetFourierAverage_le_abs`, `FABL.oxrRandomSubsetAbsFourierAverage_le_sqrt_of_lt_card`, `FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`.

**Caveat.** The informal statement describes the subset sampling in words; the proof follows the formal averages and their stated bounds.
