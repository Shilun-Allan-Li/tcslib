<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AverageInfluence.lean :: FABL.one_sub_inverse_dimension_pow_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for an Inverse-Dimension Power

**Claim.** For natural numbers $n,k$ with $0<n$ and $k\le n$, $(1-\exp(-2))k/n\le1-(1-2/n)^k$, with the fractions viewed as real numbers.

**Proof.** First handle $n=1$. Then $k$ is either $0$ or $1$, and direct evaluation gives the inequality in both cases. Now suppose $n>1$, and put $a=1-2/n$. Then $0\le a\le1$. The exponential comparison (`FABL.one_sub_two_mul_pow_le_exp_neg_two`), applied with $\delta=1/n$ and exponent $n$, gives $a^n\le\exp(-2)$. Also, for $k\le n$, the power comparison for numbers in $[0,1]$ (`FABL.natCast_mul_one_sub_pow_le`) gives $k(1-a^n)\le n(1-a^k)$. Combining these inequalities yields $k(1-\exp(-2))\le n(1-a^k)$. Divide by the positive number $n$ and substitute $a=1-2/n$ to obtain the result.

**Key facts.** `FABL.one_sub_two_mul_pow_le_exp_neg_two`, `FABL.natCast_mul_one_sub_pow_le`.
