<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.localExpectedValue_le_replace_bestLocalLabel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replacing a Law by Its Best Local Label

**Claim.** Replacing the law at any variable by the point mass at a best local label does not decrease the instance’s local expected value.

**Proof.** Fix the variable being changed. The expected affected-constraint count is the average, under its current law, of the affected count conditional on fixing that variable to a particular label (`average_affectedConditionalCount`). Every such conditional count is at most the count for the selected maximizing label (`pmfExpectation_le_bestLocalLabel`), so the sum of expected indicators over affected constraints does not decrease. The unaffected constraints have exactly the same expected indicators before and after replacement, since their scopes do not contain this variable (`localExpectedIndicator_replace_of_not_mem`). The affected and unaffected multisets partition all constraints (`affectedConstraints_add_unaffectedConstraints`); adding the two contributions therefore shows that the total expected count does not decrease. Dividing by the positive number of constraints preserves the inequality and gives the claimed comparison of local expected values.

**Key facts.** `FABL.CSPInstance.average_affectedConditionalCount`, `FABL.CSPInstance.pmfExpectation_le_bestLocalLabel`, `FABL.CSPConstraint.localExpectedIndicator_replace_of_not_mem`, `FABL.CSPInstance.affectedConstraints_add_unaffectedConstraints`.
