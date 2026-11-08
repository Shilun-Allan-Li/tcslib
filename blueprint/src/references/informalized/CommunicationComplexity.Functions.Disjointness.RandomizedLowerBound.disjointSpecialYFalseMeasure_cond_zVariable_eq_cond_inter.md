<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated conditioning on intersecting events

**Claim.** Conditioning the disjoint-conditioned measure first on Bob's special bit being false and then on a value of $Z$ gives the same measure as conditioning directly on the intersection of those two events.

**Proof.** The measure conditioned first on the special-bit-false event is then conditioned on the fiber where $Z=z$. The rule for successive conditioning identifies this iterated conditional measure with conditioning the original disjoint-conditioned measure on the intersection of the two events (`cond_cond_eq_cond_inter`). The special-bit event and the fiber are measurable in this finite sample space, as required by that rule.
