<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.expectedPayoff_eq_localExpectedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected payoff and local expected value

**Claim.** For independent random labels with the specified laws, the expected fraction of satisfied constraints equals the instance’s local expected value.

**Proof.** The joint law of the assignment is the independent product of the variable laws, so the expected payoff is the expectation of the assignment’s value under that product law. Apply the product-law payoff identity for a finite list of variables made pure (`FABL.CSPInstance.pmfExpectation_value_eq_localExpectedValue_of_pure_off`): it equates this expectation with the local expected value whenever every variable outside the list already has a point-mass law. Taking the list to contain all variables leaves no variables outside it, so the condition holds vacuously and yields the claim.

**Key facts.** `FABL.CSPInstance.pmfExpectation_value_eq_localExpectedValue_of_pure_off`.
