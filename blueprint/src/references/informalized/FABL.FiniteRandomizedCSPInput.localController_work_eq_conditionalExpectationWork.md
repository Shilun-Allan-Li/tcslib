<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.FiniteRandomizedCSPInput.localController_work_eq_conditionalExpectationWork -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Controller Work Identity

**Claim.** The work of the input’s local controller equals the total conditional-expectation work, the sum over all variables of the work of the corresponding local conditional step.

**Proof.** Unfolding the local controller identifies it as the result of running the local conditional steps on the initial local state, with the variables listed in canonical order. The work accumulated by such a run is its initial work plus the sum of the step works (`FABL.CSPInstance.runLocalConditionalSteps_work`). The initial state has zero work, and the canonical list contains every variable exactly once; thus this sum is precisely the sum over all variables defining conditional-expectation work. This gives the claimed equality.

**Key facts.** `FABL.CSPInstance.runLocalConditionalSteps_work`.
