<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.sum_cast_choose_div_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial sum with reciprocal denominators

**Claim.** For every nonnegative integer $m$, $\displaystyle\sum_{j=0}^{m}\frac{\binom{m}{j}}{j+1}=\frac{2^{m+1}-1}{m+1}$.

**Proof.** For each $j$ in the summation range, use the identity $\binom{m}{j}/(j+1)=\binom{m+1}{j+1}/(m+1)$ (the casted form is `FABL.cast_choose_div_succ`). Factor the constant denominator out of the sum. The resulting numerator sums $\binom{m+1}{j+1}$ for $0\le j\le m$, which is the sum of all binomial coefficients of order $m+1$ except the $j=0$ term. By the binomial theorem, the full sum is $2^{m+1}$, and the omitted term is $1$. Dividing the remainder by $m+1$ proves the formula.

**Key facts.** `FABL.cast_choose_div_succ`.
