<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.rawZVariable_dualProtocol_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dualization of the Raw Statistic

**Claim.** Forming the raw statistic from the dual protocol and dual hard sample gives the dual of the original raw statistic.

**Proof.** The raw statistic has four components: transcript, special coordinate, Alice’s bits before the special coordinate, and Bob’s bits after it. Equality of such records follows by checking these fields. The transcript of the dual protocol on the dual sample is the dual transcript transform of the original transcript (\texttt{message_dualProtocol_dualHardSample}). The special coordinate is reversed by the definition of the dual sample, so the two special-coordinate fields agree. Finally, the dual sample’s Alice-before vector is the reversal of the original Bob-after vector (\texttt{xBeforeSpecial_dualHardSample}), and its Bob-after vector is the reversal of the original Alice-before vector (\texttt{yAfterSpecial_dualHardSample}). Thus all four components agree, and the raw statistics are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.message_dualProtocol_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.RawZType.ext`.
