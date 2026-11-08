<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.exists_event_abs_measureReal_sub_eq_half_totalVariation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An event attains half the total variation

**Claim.** There is a measurable event whose absolute signed-measure difference under $\mu$ and $\nu$ equals half the total variation of their signed difference on the whole space.

**Proof.** The Jordan decomposition of the signed difference supplies a measurable set on which the absolute signed measure equals half its total variation (`exists_event_abs_signedMeasureDiff_eq_half_totalVariation`). Use that set as the desired event. For measurable sets, the signed difference evaluated on the event is the difference of the two measures there; substituting this identity gives the claimed equality.

**Key facts.** `CommunicationComplexity.TVDistance.exists_event_abs_signedMeasureDiff_eq_half_totalVariation`.
