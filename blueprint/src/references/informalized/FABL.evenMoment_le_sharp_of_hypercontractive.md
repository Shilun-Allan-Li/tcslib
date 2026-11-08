<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.evenMoment_le_sharp_of_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp Even Moment Bound

**Claim.** Under the stated normalization, vanishing odd moments, sharpness of the preceding even moments, and hypercontractivity, the $2j$-th moment is at most its sharp bound.

**Proof.** First, every coefficient gap of order $l<j$ is zero. At $l=0$ this follows directly from the constant-moment identity; for $1\le l<j$, the assumed sharpness of that moment gives zero gap by `evenMomentCoefficientGap_eq_zero_of_sharp`.

Fix $t=1/(n+1)>0$. Hypercontractivity, together with the second-moment normalization and the vanishing odd moments, gives a nonpositive weighted sum of all coefficient gaps (`sum_evenMomentCoefficientGap_mul_pow_le_zero`). Separate the terms below $j$, the term at $j$, and those above it. The first group vanishes, and the remaining higher terms equal minus $t^{2j}$ times the higher coefficient tail, by `coefficientGap_mul_pow_add_higher` and `higher_sum_eq_neg_pow_mul_tail`. Dividing by the positive factor $t^{2j}$ yields that the gap at $j$ is at most this higher tail.

Now take $t=1/(n+1)$ along the sequence of natural numbers $n$. The higher tail tends to zero (`higherEvenMomentCoefficientTail_tendsto_zero`), so the gap at $j$ is nonpositive. The equivalence between a nonpositive gap and the sharp moment bound (`evenMomentCoefficientGap_le_zero_iff`) gives the desired estimate.

**Key facts.** `FABL.pmfExpectation_const`, `FABL.evenMomentCoefficientGap_eq_zero_of_sharp`, `FABL.sum_evenMomentCoefficientGap_mul_pow_le_zero`, `FABL.coefficientGap_mul_pow_add_higher`, `FABL.higher_sum_eq_neg_pow_mul_tail`, `FABL.higherEvenMomentCoefficientTail_tendsto_zero`, `FABL.evenMomentCoefficientGap_le_zero_iff`.
