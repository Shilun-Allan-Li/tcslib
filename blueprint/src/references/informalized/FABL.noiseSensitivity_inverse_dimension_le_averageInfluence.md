<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AverageInfluence.lean :: FABL.noiseSensitivity_inverse_dimension_le_averageInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse-Dimension Noise Sensitivity Bound

**Claim.** For a Boolean function on a positive-dimensional sign cube, its noise sensitivity at rate $1/n$ is at most its average influence.

**Proof.** Put $\delta=1/n$. The Fourier formula for twice the noise sensitivity (`two_mul_noiseSensitivity_eq_sum_fourier`) expresses it as a sum with coefficient $1-(1-2\delta)^{|S|}$ multiplying $\widehat f(S)^2$. For each $S$, the inverse-dimension power bound (`one_sub_inverse_dimension_pow_upper`) gives $1-(1-2/n)^{|S|}\le 2|S|/n$. Since $\widehat f(S)^2\ge0$, multiplying these coefficient bounds by the squared Fourier coefficients and summing preserves the inequality. The total-influence Fourier formula (`totalInfluence_eq_sum_card_mul_sq_fourierCoeff`) identifies the resulting upper sum as $2/n$ times total influence. Dividing by $2$ yields noise sensitivity at most total influence divided by $n$, which is the average influence.

**Key facts.** `FABL.one_sub_inverse_dimension_pow_upper`, `FABL.two_mul_noiseSensitivity_eq_sum_fourier`, `FABL.totalInfluence_eq_sum_card_mul_sq_fourierCoeff`.
