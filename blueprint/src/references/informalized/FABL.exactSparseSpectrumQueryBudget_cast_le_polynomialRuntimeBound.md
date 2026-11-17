<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumQueryBudget_cast_le_polynomialRuntimeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Budget Runtime Bound

**Claim.** For all natural numbers $n,k$, the exact sparse spectrum query budget is at most $1+2^{171}\bigl(12(n+1)(2^k+1)^2\bigr)^{100}$.

**Proof.** If $n>0$, take the exact sparse spectrum Goldreich–Levin input. Its query budget is at most its polynomial runtime bound (`DeterministicGoldreichLevinInput.queryBudget_cast_le_polynomialRuntimeBound`). The input's runtime scale is at most $12$ times the stated scale (`exactSparseSpectrumGoldreichLevinInput_runtimeScale_le`), and the scale is nonnegative, so raising both sides to the hundredth power preserves the inequality. Its polynomial bound is therefore at most $2^{170}(12(n+1)(2^k+1)^2)^{100}$, which is no larger than the claimed bound with coefficient $2^{171}$ and the additional $1$. If $n=0$, the query budget is $1$ by definition, which is also at most the claimed expression because the added power term is nonnegative.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.queryBudget_cast_le_polynomialRuntimeBound`, `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.exactSparseSpectrumGoldreichLevinInput_runtimeScale_le`.
