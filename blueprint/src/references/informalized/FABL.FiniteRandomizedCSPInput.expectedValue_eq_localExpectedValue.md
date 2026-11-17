<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.FiniteRandomizedCSPInput.expectedValue_eq_localExpectedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Value as Local Expected Value

**Claim.** The randomized assignment’s expected fraction of satisfied constraint occurrences equals the sum of the constraints’ local satisfaction probabilities divided by the number of constraint occurrences.

**Proof.** The expected value is the assignment’s expected payoff when the payoff is the fraction of satisfied constraints. The general identity equating that expected payoff with the local expected value (`CSPInstance.expectedPayoff_eq_localExpectedValue`) applies directly to this instance and assignment, yielding the result.

**Key facts.** `FABL.CSPInstance.expectedPayoff_eq_localExpectedValue`.
