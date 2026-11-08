<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearner_work_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial work bound for the learner

**Claim.** For every admissible input and every sign-valued Boolean target on its cube, the learner’s charged work is at most $2^{170}\left((n+1)(M+1)/\rho\right)^{100}$.

**Proof.** The resource bounds for the learner show that its charged work is at most the deterministic work budget (deterministicGoldreichLevinLearner_resource_bounds). Casting this natural-number inequality to the real numbers preserves the order. The work-budget estimate then bounds that real-valued budget by the polynomial runtime bound (workBudget_cast_le_polynomialRuntimeBound). By the definition of the polynomial runtime bound and the input’s runtime scale, this is $2^{170}\left((n+1)(M+1)/\rho\right)^{100}$, as claimed.

**Key facts.** `FABL.deterministicGoldreichLevinLearner_resource_bounds`, `FABL.DeterministicGoldreichLevinInput.workBudget_cast_le_polynomialRuntimeBound`.
