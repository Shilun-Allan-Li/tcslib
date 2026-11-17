<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_singleton_flipSpecialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipped samples have equal singleton mass

**Claim.** A hard sample and the sample obtained by flipping Alice's special bit have equal real-valued singleton volume mass.

**Proof.** The ambient volume is uniform on the finite hard-sample space. Under a uniform measure, the real mass of any set is its cardinality divided by the cardinality of the whole space (`CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`). Both sets here are singletons, hence have cardinality one, so their masses agree.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`.
