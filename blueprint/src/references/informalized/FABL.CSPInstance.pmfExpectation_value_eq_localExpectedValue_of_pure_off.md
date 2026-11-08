<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.pmfExpectation_value_eq_localExpectedValue_of_pure_off -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation with Deterministic Coordinates

**Claim.** The expected value of the CSP instance under the independent product law equals its local expected value whenever every variable outside the given finite list has a deterministic law.

**Proof.** Proceed by induction on the list of variables, allowing the family of laws to vary. If the list is empty, every variable has a deterministic law. Choose its label to obtain an assignment; the entire product law is then concentrated at that assignment. Its expectation is the value there, and the local expected value under deterministic marginals is the same, by the deterministic-product and deterministic-local-value identities (`independentProductPMF_pure`, `pmfExpectation_pure`, and `localExpectedValue_pure`).

For a list beginning with a variable $v$, first average over the label drawn from its current law. Replacing the marginal at $v$ by the point mass at that label gives the conditional product law, and averaging these conditional expectations recovers the original product expectation (`pmfExpectation_replace_independentProductPMF`). The corresponding average of the conditional local expected values also recovers the original local expected value (`average_localExpectedValue_replace`). Thus it remains to compare the two conditional quantities for each label. In the updated law, $v$ is deterministic; every variable outside the remaining list was already deterministic, and updating the marginal at $v$ leaves those other marginals unchanged. The induction hypothesis therefore identifies the conditional product expectation with the conditional local expected value for each label. Averaging gives the desired equality.

**Key facts.** `FABL.independentProductPMF_pure`, `FABL.pmfExpectation_pure`, `FABL.CSPInstance.localExpectedValue_pure`, `FABL.pmfExpectation_replace_independentProductPMF`, `FABL.CSPInstance.average_localExpectedValue_replace`.
