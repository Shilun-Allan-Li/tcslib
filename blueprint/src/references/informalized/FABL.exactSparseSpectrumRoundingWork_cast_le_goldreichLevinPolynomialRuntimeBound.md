<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumRoundingWork_cast_le_goldreichLevinPolynomialRuntimeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rounding Work Runtime Bound

**Claim.** For a deterministic Goldreich–Levin input, the exact sparse spectrum rounding work is at most $2^{170}R^{100}$, where $R$ is its runtime scale; in particular this applies to the parameters described in the statement.

**Proof.** Write $R$ for the input's runtime scale. The runtime-scale bounds give $R\ge1$ (`DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`). The active-cap estimate bounds the cap plus one by $2^{13}R^8$ (`DeterministicGoldreichLevinInput.activeCap_add_one_cast_le_runtimeScale`), so the rounding work, which is the cap, obeys the same upper bound. Since $R\ge1$, we have $R^8\le R^{100}$. Finally $2^{13}\le2^{170}$, giving the claimed estimate.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.DeterministicGoldreichLevinInput.activeCap_add_one_cast_le_runtimeScale`.
