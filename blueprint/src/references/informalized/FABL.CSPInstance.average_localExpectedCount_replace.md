<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.average_localExpectedCount_replace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaging the expected constraint count

**Claim.** Replacing one variable’s law by a point mass at a label sampled from its original law preserves the instance’s expected satisfaction count on average.

**Proof.** Partition the constraints into those containing the variable and those omitting it. For each constraint in the latter group, replacing the variable’s marginal does not change its expected satisfaction indicator, because that variable is absent from its scope (`FABL.CSPConstraint.localExpectedIndicator_replace_of_not_mem`). Thus, for each sampled label, the count after replacement is the conditional count on affected constraints plus the fixed original count on unaffected constraints. Average this sum: linearity of expectation (`FABL.pmfExpectation_add`) separates the two terms, and the expectation of the constant unaffected contribution is that contribution (`FABL.pmfExpectation_const`). The average-affected-count identity (`FABL.CSPInstance.average_affectedConditionalCount`) turns the first term into the original count over affected constraints. Combining both parts recovers the full original count using the affected/unaffected partition (`FABL.CSPInstance.affectedConstraints_add_unaffectedConstraints`).

**Key facts.** `FABL.CSPConstraint.localExpectedIndicator_replace_of_not_mem`, `FABL.CSPInstance.affectedConstraints_add_unaffectedConstraints`, `FABL.pmfExpectation_add`, `FABL.CSPInstance.average_affectedConditionalCount`, `FABL.pmfExpectation_const`.
