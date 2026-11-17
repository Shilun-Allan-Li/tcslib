<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.majorityNoiseSensitivityLimit_sub_two_div_pi_mul_sqrt_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise-Sensitivity Limit Error Estimate

**Claim.** As $\delta$ tends to zero through nonnegative values, $\arccos(1-2\delta)/\pi-(2/\pi)\sqrt\delta$ is $O(\delta^{3/2})$.

**Proof.** The estimate for the inverse cosine states that $\arccos(1-2\delta)-2\sqrt\delta$ is $O(\delta^{3/2})$ (`FABL.arccos_one_sub_two_mul_sub_two_mul_sqrt_isBigO`). Multiplying this error by the constant $1/\pi$ preserves the order bound. The resulting expression is exactly $\arccos(1-2\delta)/\pi-(2/\pi)\sqrt\delta$, giving the claim.

**Key facts.** `FABL.arccos_one_sub_two_mul_sub_two_mul_sqrt_isBigO`.
