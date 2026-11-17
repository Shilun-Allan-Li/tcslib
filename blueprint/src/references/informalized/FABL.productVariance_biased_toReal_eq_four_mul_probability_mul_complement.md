<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productVariance_biased_toReal_eq_four_mul_probability_mul_complement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a biased Boolean function

**Claim.** For a sign-valued Boolean function under the product law with parameter $0<p<1$, its variance is $4q_f(p)(1-q_f(p))$, where $q_f(p)$ is the probability polynomial for output $-1$.

**Proof.** The polynomial defining $q_f(p)$ agrees with the probability of output $-1$ (\texttt{biasedMinusProbabilityPolynomial\_eq}). For a sign-valued function, the mean equals one minus twice this probability (\texttt{productMean\_toReal\_eq\_one\_sub\_two\_mul\_minusProbability}), while its variance equals one minus the square of its mean (\texttt{productVariance\_toReal\_eq\_one\_sub\_sq\_mean}). Substituting the mean gives $1-(1-2q_f(p))^2=4q_f(p)(1-q_f(p))$.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_eq`, `FABL.productMean_toReal_eq_one_sub_two_mul_minusProbability`, `FABL.productVariance_toReal_eq_one_sub_sq_mean`.
