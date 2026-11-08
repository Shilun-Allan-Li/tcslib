<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumWorkBudget_cast_le_polynomialRuntimeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Budget Runtime Bound

**Claim.** For all natural numbers $n,k$, the exact sparse spectrum work budget is at most $1+2^{171}\bigl(12(n+1)(2^k+1)^2\bigr)^{100}$.

**Proof.** When $n>0$, use the exact sparse spectrum Goldreich–Levin input. Its rounding work and Goldreich–Levin work budget are each bounded by that input's polynomial runtime bound, by the rounding estimate (`exactSparseSpectrumRoundingWork_cast_le_goldreichLevinPolynomialRuntimeBound`) and the work-budget estimate (`DeterministicGoldreichLevinInput.workBudget_cast_le_polynomialRuntimeBound`). Their sum is therefore at most twice that bound, namely $2^{171}$ times the hundredth power of the input's runtime scale. The scale is nonnegative and at most $12(n+1)(2^k+1)^2$ (`exactSparseSpectrumGoldreichLevinInput_runtimeScale_le`), so the resulting expression is at most the claimed bound. When $n=0$, the work budget is $1$, which is at most the claimed expression since its power term is nonnegative.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.DeterministicGoldreichLevinInput.workBudget_cast_le_polynomialRuntimeBound`, `FABL.exactSparseSpectrumGoldreichLevinInput_runtimeScale_le`, `FABL.exactSparseSpectrumRoundingWork_cast_le_goldreichLevinPolynomialRuntimeBound`.
