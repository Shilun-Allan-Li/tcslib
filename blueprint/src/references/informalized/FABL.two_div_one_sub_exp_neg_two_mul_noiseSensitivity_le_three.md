<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.two_div_one_sub_exp_neg_two_mul_noiseSensitivity_le_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity Bound

**Claim.** For a Boolean function and $\delta\in[0,1]$, $\frac{2}{1-e^{-2}}\operatorname{NS}_\delta[f]\le 3\operatorname{NS}_\delta[f]$.

**Proof.** The scalar estimate $2/(1-e^{-2})\le 3$ (`FABL.two_div_one_sub_exp_neg_two_le_three`) can be multiplied by the noise sensitivity because noise sensitivity is nonnegative (`FABL.noiseSensitivity_nonneg`). Multiplication by this nonnegative quantity preserves the inequality and gives the stated bound.

**Key facts.** `FABL.two_div_one_sub_exp_neg_two_le_three`, `FABL.noiseSensitivity_nonneg`.
