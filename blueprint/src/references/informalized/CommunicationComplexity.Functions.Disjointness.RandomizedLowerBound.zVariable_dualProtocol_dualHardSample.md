<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_dualProtocol_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of the Z-Variable

**Claim.** Evaluating the $Z$-variable for the dual protocol on the dualized sample gives the dualization of the original $Z$-value.

**Proof.** Both sides are achievable $Z$-values for the dual protocol, hence are subtype elements whose underlying raw values determine them. Their raw values agree by the raw-variable duality identity: the transcript, special coordinate, and two window vectors of the dualized sample are exactly the recoding of the original raw value (`rawZVariable_dualProtocol_dualHardSample`). Equality of the underlying values therefore gives equality of the subtype elements.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.rawZVariable_dualProtocol_dualHardSample`.
