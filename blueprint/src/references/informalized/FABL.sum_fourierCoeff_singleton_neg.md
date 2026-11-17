<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/ArrowLevelOneBound.lean :: FABL.sum_fourierCoeff_singleton_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation of singleton coefficient sum

**Claim.** Negating a Boolean function negates the sum of its singleton Fourier coefficients.

**Proof.** First express the sum of singleton Fourier coefficients as the expectation of the function times the sum of the coordinate signs (`sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue`). For the negated Boolean function, its real-valued version is the pointwise negative of the original (`BooleanFunction.toReal_neg`). Thus the integrand is the negative of the original integrand. Linearity of finite expectation with respect to negation then gives the negative of the original coefficient sum.

**Key facts.** `FABL.sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue`, `FABL.BooleanFunction.toReal_neg`.
