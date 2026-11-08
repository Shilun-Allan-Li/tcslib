<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.tendsto_biasedMinusProbabilityPolynomial_majority_odd_of_lt_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased majority error below half

**Claim.** For fixed $p\in(0,1/2)$, the probability that the majority of $2m+1$ independent signs is $-1$ tends to zero as $m\to\infty$.

**Proof.** Set $d=1/2-p>0$. The error probability is nonnegative, since it lies in $(0,1)$ by the interior-bias bound for monotone, nonconstant odd majority (majority_monotone; majority_odd_isNonconstant; biasedMinusProbabilityPolynomial_mem_Ioo).

For each $m$, put $C=d\sqrt{2m+1}$. This satisfies the hypotheses of the lower-bias majority tail estimate, and $1/2-C/\sqrt{2m+1}=p$. That estimate bounds the biased error by $2\exp(-2C^2)$. The equality between polynomial error and biased probability (biasedMinusProbabilityPolynomial_eq) transfers this bound to the quantity in the theorem. The exponential term is at most the fixed-bias error bound associated with $d$, which tends to zero (tendsto_fixedBiasMajorityError_zero). The squeeze theorem now gives the required limit.

**Key facts.** `FABL.majority_monotone`, `FABL.majority_odd_isNonconstant`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`, `FABL.biasedMinusProbability_majority_lower_le_two_mul_exp`, `FABL.biasedMinusProbabilityPolynomial_eq`, `FABL.tendsto_fixedBiasMajorityError_zero`.
