<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualZValue_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Z-value dualization

**Claim.** The dualization map on achievable $Z$-values is injective.

**Proof.** Suppose two achievable $Z$-values have the same dual. Their underlying raw $Z$-values are then equal, by applying injectivity of raw $Z$-value dualization (`dualRawZValue_injective`) to the equality of the underlying values. Achievable $Z$-values are subtypes of raw $Z$-values, so equality of their underlying values gives equality of the subtype elements. Therefore the dualization map is injective.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualRawZValue_injective`.
