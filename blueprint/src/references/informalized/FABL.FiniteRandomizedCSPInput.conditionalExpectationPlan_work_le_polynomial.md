<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.FiniteRandomizedCSPInput.conditionalExpectationPlan_work_le_polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound on Plan Work

**Claim.** The work of the conditional-expectation plan is at most the stated polynomial in the number of variables and constraint occurrences.

**Proof.** The plan’s work equals the conditional-expectation work, by the local-controller work identity (`localController_work_eq_conditionalExpectationWork`). Applying the bound on conditional-expectation work (`conditionalExpectationWork_le_polynomial`) gives the claimed inequality.

**Key facts.** `FABL.FiniteRandomizedCSPInput.localController_work_eq_conditionalExpectationWork`, `FABL.FiniteRandomizedCSPInput.conditionalExpectationWork_le_polynomial`.
