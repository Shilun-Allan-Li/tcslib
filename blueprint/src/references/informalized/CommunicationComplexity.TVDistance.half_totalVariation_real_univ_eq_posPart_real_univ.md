<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.half_totalVariation_real_univ_eq_posPart_real_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half total variation equals positive mass

**Claim.** For the signed difference of two probability measures, half its total variation on the whole space equals the mass of its positive Jordan part there.

**Proof.** The total variation of a signed measure is the sum of the masses of its positive and negative Jordan parts (`totalVariation_real_univ`). For the difference of two probability measures, those two parts have equal mass on the whole space (`jordan_posPart_real_univ_eq_negPart_real_univ`). Substituting this equality into the sum shows that half the total variation is exactly the positive-part mass.

**Key facts.** `CommunicationComplexity.TVDistance.totalVariation_real_univ`, `CommunicationComplexity.TVDistance.jordan_posPart_real_univ_eq_negPart_real_univ`.
