<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_eq_cond_specialYFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning on Bob's special bit

**Claim.** If the fiber measure gives positive mass to the event that Bob's special bit is false, then Alice's special-bit law equals the pushforward of the fiber measure conditioned on that event.

**Proof.** Apply the result for conditioning a special-bit law under a product pair law to the product decomposition of the conditional pair law, taking Bob's bit value to be false. The hypothesis supplies the required nonzero mass for this conditioning. The resulting identity is precisely that Alice's conditional law is the pushforward under her special-bit map of the fiber measure conditioned on Bob's special bit being false.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_eq_prod`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_eq_cond_specialY_of_prod`.
