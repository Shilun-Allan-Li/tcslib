<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yGeSpecial_specialCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the special coordinate

**Claim.** Evaluating Bob’s truncated input vector at the special coordinate gives Bob’s bit at that coordinate.

**Proof.** At $i=T$, the condition $T\le i$ holds with equality, so the truncated vector retains Bob’s bit there. By the definition of Bob’s bit at the special coordinate, that value is $y_T$, as claimed.
