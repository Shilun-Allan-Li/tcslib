<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaBalancedExponent_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced Exponent Nonnegativity

**Claim.** For a positive rational matrix exponent $\omega$ and a natural number $k$, the balanced exponent is nonnegative.

**Proof.** The balanced exponent is $\omega k/(\omega+1)$. Its numerator is nonnegative because $\omega>0$ and $k\ge0$, and its denominator is positive because `positiveMatrixExponent_add_one_pos` gives $\omega+1>0$. A quotient with nonnegative numerator and positive denominator is nonnegative.

**Key facts.** `FABL.positiveMatrixExponent_add_one_pos`.
