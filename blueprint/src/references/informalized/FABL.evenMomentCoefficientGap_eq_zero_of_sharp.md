<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.evenMomentCoefficientGap_eq_zero_of_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing gap at the sharp moment bound

**Claim.** When the even moment equals its sharp bound, the corresponding even-moment coefficient gap is zero.

**Proof.** Expand the definition of the coefficient gap and substitute the assumed moment value. The sharp coefficient identity (`sharp_even_coefficient_mul_bound`) says that multiplying this bound by the binomial coefficient and the prescribed noise factor yields the binomial coefficient being subtracted. The two terms therefore cancel, leaving zero.

**Key facts.** `FABL.sharp_even_coefficient_mul_bound`.
