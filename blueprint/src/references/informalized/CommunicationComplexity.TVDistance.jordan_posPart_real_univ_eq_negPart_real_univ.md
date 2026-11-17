<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.jordan_posPart_real_univ_eq_negPart_real_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal Jordan-part masses

**Claim.** For probability measures $\mu$ and $\nu$, the positive and negative parts of their signed measure difference have equal total mass on $\Omega$.

**Proof.** Apply the Jordan decomposition identity to the measurable set $\Omega$: the signed measure difference on $\Omega$ is the positive-part mass minus the negative-part mass. The signed measure difference vanishes on the whole space, since both probability measures have total mass one (`signedMeasureDiff_univ`). Thus the difference of the two Jordan-part masses is zero, so they are equal.

**Key facts.** `CommunicationComplexity.TVDistance.signedMeasure_apply_eq_posPart_sub_negPart`, `CommunicationComplexity.TVDistance.signedMeasureDiff_univ`.
