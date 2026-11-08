<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/SubGaussian.lean :: mgf_centered_sq_le_of_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered-square MGF bound for nonnegative parameters

**Claim.** Under the stated sub-Gaussian MGF hypothesis, for $0\le t\le 1/(4\sigma^2)$ the centered square has an integrable exponential and its MGF is at most $e^{2\sigma^4t^2}$.

**Proof.** Set $a=\sigma^2t$. The parameter assumptions give $0\le a\le1/4$, hence $2\sigma^2t<1$. The sub-Gaussian square-exponential estimate (integral_exp_mul_sq_le_of_subgaussian) then gives integrability of $e^{tZ^2}$ and bounds its expectation by $(1-2a)^{-1/2}$. Since $e^{t(Z^2-\sigma^2)}=e^{-a}e^{tZ^2}$, the centered exponential is integrable and its expectation is bounded by $e^{-a}(1-2a)^{-1/2}$. Taking logarithms of this last expression gives $-a-\tfrac12\log(1-2a)$, which is at most $2a^2$ by the logarithmic inequality (neg_log_one_sub_two_mul_le_two_sq), applicable because $|a|\le1/4$. Exponentiating and using $a^2=\sigma^4t^2$ proves the claimed bound.

**Key facts.** `integral_exp_mul_sq_le_of_subgaussian`, `neg_log_one_sub_two_mul_le_two_sq`.
