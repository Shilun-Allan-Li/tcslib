<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.average_localExpectedValue_replace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaging the expected value

**Claim.** Replacing one variable’s law by a point mass at a label sampled from its original law preserves the instance’s expected fraction of satisfied constraints on average.

**Proof.** The expected value is the expected count divided by the fixed number of constraints. Rewrite this division as multiplication by the reciprocal of that fixed denominator. Expectation commutes with multiplication by a constant (`FABL.pmfExpectation_mul_const`), so the asserted equality follows from the averaging identity for the expected count (`FABL.CSPInstance.average_localExpectedCount_replace`).

**Key facts.** `FABL.pmfExpectation_mul_const`, `FABL.CSPInstance.average_localExpectedCount_replace`.
