<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LTFNoiseSensitivityDerivative.lean :: FABL.fourierWeightAbove_pred_le_four_div_sqrt_of_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier tail bound for linear thresholds

**Claim.** If $f$ is a linear threshold function and $k>0$, then its Fourier weight above level $k-1$ is at most $4/\sqrt{k}$.

**Proof.** If $k=1$, the tail is a sub-sum of the total squared Fourier coefficient sum, since every omitted summand is nonnegative. Parseval's identity for Boolean-valued functions gives total weight $1$, which is at most $4$. Now suppose $k\ge2$ and choose noise rate $\delta=1/k$. Put $c=1-e^{-2}>0$. For every subset with $|S|>k-1$, integrality gives $|S|\ge k=1/\delta$. The exponential estimate for $(1-2\delta)^{|S|}$ therefore gives $(1-2\delta)^{|S|}\le e^{-2}$, hence $c\le1-(1-2\delta)^{|S|}$. Multiplying by the nonnegative squared Fourier coefficient and summing over this tail bounds $c$ times its weight by the corresponding full Fourier sum. The Fourier formula for noise sensitivity identifies that full sum with twice the noise sensitivity. Since $2/(1-e^{-2})\le3$ and noise sensitivity is nonnegative, division by $c$ yields a tail bound of three times the noise sensitivity. Peres's noise-sensitivity bound for linear threshold functions now gives at most $3\sqrt{3/2}\sqrt\delta$. Substituting $\delta=1/k$ and using $3\sqrt{3/2}\le4$ proves the result.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.one_sub_two_mul_pow_le_exp_neg_two`, `FABL.two_mul_noiseSensitivity_eq_sum_fourier`, `FABL.two_div_one_sub_exp_neg_two_le_three`, `FABL.noiseSensitivity_nonneg`, `FABL.peresNoiseSensitivityBound`.
