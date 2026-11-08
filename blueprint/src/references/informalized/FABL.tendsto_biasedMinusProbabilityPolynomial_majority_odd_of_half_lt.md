<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.tendsto_biasedMinusProbabilityPolynomial_majority_odd_of_half_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased majority error above half

**Claim.** For fixed $p\in(1/2,1)$, the probability that the majority of $2m+1$ independent signs is $-1$ tends to $1$ as $m\to\infty$.

**Proof.** Set $d=p-1/2>0$. The error probability lies in $(0,1)$ for each odd majority, using monotonicity and nonconstancy of odd majority (majority_monotone; majority_odd_isNonconstant) together with the fact that the biased error polynomial lies strictly between zero and one at interior biases (biasedMinusProbabilityPolynomial_mem_Ioo). Thus its complement is nonnegative.

For each $m$, choose $C=d\sqrt{2m+1}$. This choice satisfies the admissibility condition in the majority tail bound, and $1/2+C/\sqrt{2m+1}=p$. The exponential upper bound on the complementary error (one_sub_two_mul_exp_le_biasedMinusProbability_majority_upper), together with the identification of the polynomial error with the biased probability (biasedMinusProbabilityPolynomial_eq), bounds the complement by $2\exp(-2C^2)$. This in turn is at most the fixed-bias error bound associated with $d$. That bound tends to zero as $m\to\infty$ (tendsto_fixedBiasMajorityError_zero). Squeezing shows that the complement tends to zero, so the error probability tends to one.

**Key facts.** `FABL.majority_monotone`, `FABL.majority_odd_isNonconstant`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`, `FABL.one_sub_two_mul_exp_le_biasedMinusProbability_majority_upper`, `FABL.biasedMinusProbabilityPolynomial_eq`, `FABL.tendsto_fixedBiasMajorityError_zero`.
