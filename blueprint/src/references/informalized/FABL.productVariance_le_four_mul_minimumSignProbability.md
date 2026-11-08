<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productVariance_le_four_mul_minimumSignProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance and Minority Sign Probability

**Claim.** For a sign-valued function on a finite product space, its variance is at most four times the smaller of the probabilities that it equals $1$ and $-1$.

**Proof.** Let $p_+$ and $p_-$ be the probabilities of the two signs. Since the function takes only the values $-1$ and $1$, the two events partition the space, so $p_++p_-=1$. Linearity and normalization of expectation give this identity, and nonnegativity of expectation gives $p_+,p_-\ge 0$. The mean of the function is $p_+-p_-$, while its second moment is $1$. The variance identity expressing variance as second moment minus the square of the mean therefore gives $1-(p_+-p_-)^2=4p_+p_-$. If $p_+\le p_-$, then $p_-\le 1$, so $4p_+p_-\le4p_+$; if $p_-\le p_+$, then $p_+\le1$, so $4p_+p_-\le4p_-$. In either case this is the desired bound by four times the smaller probability.

**Key facts.** `FABL.pmfExpectation_nonneg`, `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_sub_general`, `FABL.pmfExpectation_sq_eq_one_of_hasSignRange`, `FABL.productVariance_eq_secondMoment_sub_mean_sq`.
