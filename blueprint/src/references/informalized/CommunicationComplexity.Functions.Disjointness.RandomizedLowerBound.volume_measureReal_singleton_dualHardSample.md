<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_singleton_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual samples have equal singleton mass

**Claim.** A hard sample and its dual have equal real-valued singleton volume mass.

**Proof.** The ambient volume is uniform on the finite hard-sample space. For a uniform measure, the real mass of a set is the number of its elements divided by the size of the whole space (`CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`). Each singleton has one element, so the singleton of the dual sample and the singleton of the original sample have the same mass.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`.
