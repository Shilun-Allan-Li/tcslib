<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.binomialHalfEvenReciprocalSum_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even reciprocal binomial sum

**Claim.** For every natural number $m$, $\displaystyle\sum_{j=0}^{m}\binom{m}{j}\frac{1}{2^m}\frac{1}{2j+2}=\frac{1-2^{-(m+1)}}{m+1}$.

**Proof.** For each summand, combine the factor $2^{-m}$ with $(2j+2)^{-1}$ to obtain $2^{-(m+1)}(j+1)^{-1}$. Thus the sum is $2^{-(m+1)}$ times $\sum_{j=0}^m\binom mj/(j+1)$. The identity `sum_cast_choose_div_succ` evaluates this latter sum as $(2^{m+1}-1)/(m+1)$. Multiplying by $2^{-(m+1)}$ and simplifying gives $(1-2^{-(m+1)})/(m+1)$, as claimed.

**Key facts.** `FABL.sum_cast_choose_div_succ`.
