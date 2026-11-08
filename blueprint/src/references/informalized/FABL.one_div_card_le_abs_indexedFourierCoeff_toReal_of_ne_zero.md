<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaFourierGap.lean :: FABL.one_div_card_le_abs_indexedFourierCoeff_toReal_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Fourier Coefficient Lower Bound

**Claim.** If the indexed Fourier coefficient of a sign-valued function is nonzero, its absolute value is at least the reciprocal of the size of the indexed sign cube.

**Proof.** Write the coefficient as the integer-valued Boolean Fourier numerator divided by the cardinality of the indexed sign cube, using the numerator representation (`indexedFourierCoeff_toReal_eq_numerator_div`). If that integer numerator were zero, the representation would make the coefficient zero, contrary to the hypothesis. A nonzero integer has absolute value at least $1$, so the absolute value of its real image is at least $1$. The cube has positive cardinality; dividing this bound by that positive cardinality gives the stated reciprocal lower bound.

**Key facts.** `FABL.indexedFourierCoeff_toReal_eq_numerator_div`.
