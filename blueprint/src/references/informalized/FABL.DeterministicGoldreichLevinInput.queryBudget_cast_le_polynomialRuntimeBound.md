<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.queryBudget_cast_le_polynomialRuntimeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query budget runtime bound

**Claim.** The deterministic Goldreich–Levin query budget is at most $2^{170}R^{100}$.

**Proof.** 1. Write $R$ for the runtime scale. The runtime scale bounds $1$ and the dimension, so $R\ge 1$ and $n\le R$ (the latter follows from the bound on $n+1$). The restricted-weight component estimate bounds the stage query budget by $2^{148}R^{88}$; the coefficient component estimate bounds the coefficient sample count by $2^{138}R^{88}$ (the two component bounds are supplied by `deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale` and `deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale`).

2. The list query contribution is $n$ times the stage query budget, hence is at most $2^{148}R^{89}$. Since $R\ge1$, the coefficient contribution is at most $2^{138}R^{89}$. Adding gives at most $(2^{148}+2^{138})R^{89}\le 2^{149}R^{89}$.

3. Again using $R\ge1$, we have $R^{89}\le R^{100}$. Since $2^{149}\le2^{170}$, the total query budget is at most $2^{170}R^{100}$. The scale inequalities used here are the runtime-scale factor bounds (`runtimeScale_factor_bounds`).

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale`, `FABL.deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale`.
