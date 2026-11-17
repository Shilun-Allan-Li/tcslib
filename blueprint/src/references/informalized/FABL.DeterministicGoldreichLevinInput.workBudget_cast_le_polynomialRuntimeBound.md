<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.workBudget_cast_le_polynomialRuntimeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work budget polynomial bound

**Claim.** The deterministic Goldreich–Levin work budget is at most $2^{170}R^{100}$.

**Proof.** 1. Put $R$ equal to the runtime scale. Its factor bounds show $R\ge1$ and $n\le R$ (`runtimeScale_factor_bounds`). The active-cap estimate bounds the active cap plus one by $2^{13}R^8$ (`activeCap_add_one_cast_le_runtimeScale`). The restricted and coefficient component estimates bound their construction, query, and local-work terms by, respectively, $2^{148}R^{88}$ and $2^{138}R^{88}$ (`deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale` and `deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale`).

2. The controller work is $16(n+1)^2$ times the square of the active cap plus one. Applying the dimension and cap bounds gives at most $2^{30}R^{18}$. In the stage work, the local term has an additional factor of twice the active cap, so it is at most $2^{162}R^{96}$. Raising the other terms to the common power $R^{96}$, using $R\ge1$, and adding the constants bounds the full stage work by $2^{163}R^{96}$.

3. The list work consists of restricted construction work plus $n$ times the stage work. These are bounded by $2^{148}R^{88}$ and $R\cdot2^{163}R^{96}$, so the list work is at most $2^{164}R^{97}$.

4. The coefficient work consists of coefficient construction work, sample queries, and active-cap times coefficient local work. The first two terms are each at most $2^{138}R^{88}$; the last is at most $2^{151}R^{96}$ by the active-cap and local-work bounds. Since $R\ge1$, their sum is at most $2^{152}R^{96}$.

5. Adding list and coefficient work and increasing powers using $R\ge1$ gives at most $(2^{164}+2^{152})R^{97}\le2^{165}R^{97}$. Since $R^{97}\le R^{100}$ and $2^{165}\le2^{170}$, the total is at most $2^{170}R^{100}$.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.DeterministicGoldreichLevinInput.activeCap_add_one_cast_le_runtimeScale`, `FABL.deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale`, `FABL.deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale`.
