<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPConstraint.localExpectedIndicator_pure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Indicator for a Deterministic Assignment

**Claim.** When each variable is sampled independently from the point mass at its assigned value, the expected satisfaction indicator equals one if the constraint is satisfied by that assignment and zero otherwise.

**Proof.** The independent product of point masses is the point mass at the full assignment (`FABL.independentProductPMF_pure`). The expectation of any payoff under a point mass is its value at the supported point (`FABL.pmfExpectation_pure`). Thus the local expected indicator is the satisfaction payoff evaluated on the scoped values of the assignment. This is exactly the satisfied indicator by its definition.

**Key facts.** `FABL.independentProductPMF_pure`, `FABL.pmfExpectation_pure`.
