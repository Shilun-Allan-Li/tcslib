<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_eq_cond_specialY_of_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning under a product law

**Claim.** When the conditional special-pair law is a product and Bob's specified special-bit event has positive fiber mass, Alice's special-bit law equals the pushforward of the fiber measure conditioned on that event.

**Proof.** Compare the two measures on Alice's bit space by their singleton masses. The singleton identities and the formula for the real mass of a conditioned measure reduce the comparison, at a bit $b_X$, to the fiber mass of the intersection of Alice's event and Bob's event, divided by the fiber mass of Bob's event. The intersection is exactly the event that the special pair equals $(b_X,b_Y)$. Since the pair law is a product, its singleton-factorization identity makes the intersection mass the product of the two marginal event masses. The factor for Bob's event cancels against the conditioning denominator, which is nonzero by hypothesis, leaving Alice's marginal mass. Thus all singleton masses agree, so the measures are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalPairLaw_singleton_factorization_of_eq_prod`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialYLaw_singleton`.
