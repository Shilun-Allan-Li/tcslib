<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.restrictedWeightPolynomialBudget_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted weight budget bound

**Claim.** The restricted-weight polynomial budget is at most $2^{148}R^{88}$.

**Proof.** The restricted-weight algorithm scale plus one is at most $2^{16}R^{11}$ (`restrictedWeightAlgorithmScale_add_one_cast_le_runtimeScale`). Both sides are nonnegative, so raising this inequality to the eighth power preserves it. The polynomial budget is $2^{20}$ times the eighth power of the scale plus one. Consequently it is at most $2^{20}(2^{16}R^{11})^8=2^{148}R^{88}$.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.restrictedWeightAlgorithmScale_add_one_cast_le_runtimeScale`.
