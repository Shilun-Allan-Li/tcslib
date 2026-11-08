<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Routine Runtime Bounds

**Claim.** The small-bias construction work, sample count, and local Fourier-estimation work are each at most $2^{138}R^{88}$.

**Proof.** Each of the three integer-valued work quantities is bounded by the coefficient input's polynomial budget, by `deterministicGoldreichLevinCoefficientComponents_le_polynomialBudget`. Regard these integer inequalities as inequalities of real numbers. The polynomial budget is at most $2^{138}R^{88}$ by `coefficientPolynomialBudget_cast_le_runtimeScale`. Chaining the corresponding inequalities proves all three bounds.

**Key facts.** `FABL.deterministicGoldreichLevinCoefficientComponents_le_polynomialBudget`, `FABL.DeterministicGoldreichLevinInput.coefficientPolynomialBudget_cast_le_runtimeScale`.
