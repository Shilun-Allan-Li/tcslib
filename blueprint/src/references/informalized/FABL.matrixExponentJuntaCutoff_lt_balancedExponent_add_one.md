<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaCutoff_lt_balancedExponent_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ceiling Strict Bound

**Claim.** For positive rational $\omega$ and natural number $k$, the cutoff is strictly less than the balanced exponent plus one.

**Proof.** The balanced exponent is nonnegative by `matrixExponentJuntaBalancedExponent_nonneg`. For a nonnegative rational, its natural-number ceiling is strictly less than the rational plus one. Applying this ceiling property to the balanced exponent proves the result.

**Key facts.** `FABL.matrixExponentJuntaBalancedExponent_nonneg`.
