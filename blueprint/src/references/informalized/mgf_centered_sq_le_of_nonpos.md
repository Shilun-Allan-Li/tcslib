<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/SubGaussian.lean :: mgf_centered_sq_le_of_nonpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered-square MGF bound for nonpositive parameters

**Claim.** Under the stated sub-Gaussian MGF hypothesis and second-moment identity, for $-1/(4\sigma^2)\le t\le0$ the centered square has an integrable exponential and its MGF is at most $e^{2\sigma^4t^2}$.

**Proof.** First use the sub-Gaussian fourth-moment estimate (integral_pow_four_le_of_subgaussian) to obtain integrability of $Z^4$ and $\mathbb E[Z^4]\le4\sigma^4$. Put $a=-t\sigma^2$, so $0\le a\le1/4$. For each outcome, apply the second-order bound for the exponential at a nonpositive argument (exp_neg_le_one_sub_add_sq_div_two) to get $e^{tZ^2}\le1+tZ^2+t^2Z^4/2$. Also $e^{tZ^2}\le1$, so it is integrable. Integrating the polynomial bound and using $\mathbb E[Z^2]=\sigma^2$ and $\mathbb E[Z^4]\le4\sigma^4$ yields $\mathbb E[e^{tZ^2}]\le1-a+2a^2$. The centered exponential equals $e^a e^{tZ^2}$, so it is integrable and its expectation is at most $e^a(1-a+2a^2)$. Finally, $1-a+2a^2\le e^{-a+2a^2}$ by $1+u\le e^u$; multiplying by $e^a$ gives the bound $e^{2a^2}=e^{2\sigma^4t^2}$.

**Key facts.** `integral_pow_four_le_of_subgaussian`, `exp_neg_le_one_sub_add_sq_div_two`.
