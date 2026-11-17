<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.exists_event_abs_signedMeasureDiff_eq_half_totalVariation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Event attaining half the total variation

**Claim.** There is a measurable event whose absolute signed-measure difference under $\mu$ and $\nu$ equals half the total variation of their signed difference on the whole space.

**Proof.** Let $s=\mu-\nu$, and take a measurable set $S$ from the Jordan decomposition such that the positive part vanishes on $S$ and the negative part vanishes on its complement. Choose the event $S^c$. The positive part has the same mass on $S^c$ as on the whole space, since its mass on $S$ is zero; the negative part has mass zero on $S^c$. Therefore $s(S^c)$ is the total mass of the positive part. The Jordan decomposition identity expresses $s(S^c)$ as the positive-part mass minus the negative-part mass there, and the half-total-variation identity identifies the positive-part mass on the whole space with half the total variation. This quantity is nonnegative, so taking its absolute value leaves it unchanged.

**Key facts.** `CommunicationComplexity.TVDistance.half_totalVariation_real_univ_eq_posPart_real_univ`, `CommunicationComplexity.TVDistance.signedMeasure_apply_eq_posPart_sub_negPart`.
