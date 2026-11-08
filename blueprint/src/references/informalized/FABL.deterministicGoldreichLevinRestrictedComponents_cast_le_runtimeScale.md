<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted-component runtime bounds

**Claim.** The restricted-weight construction work, stage query budget, and restricted local work are each at most $2^{148}R^{88}$ as real numbers, where $R$ is the runtime scale.

**Proof.** First use the componentwise polynomial-budget theorem: each of the three restricted quantities is at most the input’s polynomial budget (`deterministicGoldreichLevinRestrictedComponents_le_polynomialBudget`). Cast these natural-number inequalities to real inequalities. The polynomial budget itself is at most $2^{148}R^{88}$ (`DeterministicGoldreichLevinInput.restrictedWeightPolynomialBudget_cast_le_runtimeScale`). Transitivity gives the asserted bound for each quantity.

**Key facts.** `FABL.deterministicGoldreichLevinRestrictedComponents_le_polynomialBudget`, `FABL.DeterministicGoldreichLevinInput.restrictedWeightPolynomialBudget_cast_le_runtimeScale`.
