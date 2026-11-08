<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zDistance_le_xDistance_add_yDistance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variation bound for the special bit-pair

**Claim.** The total variation distance of the conditional law of the special-coordinate bit-pair from the uniform pair law is at most the sum of the distances of its two conditional bit marginals from the uniform bit law.

**Proof.** The conditional law of the special bit-pair is the product of the two conditional marginal laws (`conditionalSpecialPairLaw_eq_prod`). The uniform law on bit-pairs is likewise the product of two uniform bit laws (`uniformBoolPair_eq_prod`). The total variation distance between product probability laws is at most the sum of the total variation distances of their corresponding factors (`tvDistance_prod_le`). Substituting these two product identities gives the claimed bound.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_eq_prod`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBoolPair_eq_prod`, `CommunicationComplexity.TVDistance.tvDistance_prod_le`.
