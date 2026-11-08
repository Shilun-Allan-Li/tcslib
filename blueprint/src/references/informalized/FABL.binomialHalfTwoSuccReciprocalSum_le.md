<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.binomialHalfTwoSuccReciprocalSum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial reciprocal sum bound

**Claim.** For every natural number $m$, the binomially weighted reciprocal sum is at most $4/((m+1)(m+2))$.

**Proof.** Use the identity relating consecutive binomial coefficients to rewrite each summand: $\binom{m}{j}/((j+1)(j+2))=\binom{m+2}{j+2}/((m+1)(m+2))$ (the cast identity `FABL.cast_choose_div_two_succs`). Taking out the common denominator, the sum is therefore the sum of the shifted coefficients divided by $2^m(m+1)(m+2)$. The shifted binomial sum is at most $2^{m+2}$ by `FABL.sum_shifted_choose_le_pow`, since it uses only some of the nonnegative coefficients in the binomial expansion of $(1+1)^{m+2}$. Dividing by the positive denominator and using $2^{m+2}/2^m=4$ gives the stated bound.

**Key facts.** `FABL.cast_choose_div_two_succs`, `FABL.sum_shifted_choose_le_pow`.
