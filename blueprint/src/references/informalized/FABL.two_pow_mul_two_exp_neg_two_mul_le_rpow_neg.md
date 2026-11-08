<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.two_pow_mul_two_exp_neg_two_mul_le_rpow_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential power comparison

**Claim.** For every integer $n\ge 2$, $2^n\,2e^{-2n}\le 2^{-n}$.

**Proof.** The preceding exponential estimate gives $2^{2n+1}\le e^{2n}$. Rewriting the left side as $2^{n+1}/e^{2n}$, it suffices to show this quotient is at most $1/2^n$. Since the denominator is positive, this is equivalent to $2^{n+1}2^n\le e^{2n}$; the left side is $2^{2n+1}$, so the estimate applies. Finally, $1/2^n=2^{-n}$.

**Key facts.** `FABL.two_pow_two_mul_add_one_lt_exp_two_mul`.
