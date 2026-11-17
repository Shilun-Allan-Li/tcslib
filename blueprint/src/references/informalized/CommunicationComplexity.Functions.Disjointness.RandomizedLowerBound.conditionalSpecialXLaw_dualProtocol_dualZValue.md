<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_dualProtocol_dualZValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Special-bit law under protocol duality

**Claim.** The conditional law of Alice's special bit for the dual protocol and dual summary equals the conditional law of Bob's special bit for the original protocol and summary.

**Proof.** Both laws are measures on the two-point space of bits, so it suffices to compare their masses at each singleton. The singleton-mass identities express these as probabilities of the corresponding special-bit events within their summary fibers. The fiber-measure formula writes each such conditional probability as the volume of the fiber intersected with the bit event, divided by the volume of the fiber. Protocol duality preserves the fiber volume (volume_measureReal_zVariable_dualProtocol_dualZValue), and it identifies the dual fiber intersected with Alice's bit event with the original fiber intersected with Bob's bit event (volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX). Thus the numerators and denominators agree, so all singleton masses agree and hence the two laws are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialYLaw_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_real_apply`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_zVariable_dualProtocol_dualZValue`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX`.
