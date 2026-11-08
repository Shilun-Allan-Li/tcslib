<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinate_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of a disjoint-coordinate label

**Claim.** Under the uniform law on the three disjoint-coordinate labels, each label has mass $1/3$.

**Proof.** The uniform-measure formula `uniformOn_univ_measureReal_eq_card_subtype` gives the measure of a subset as its cardinality divided by the cardinality of the whole space. The singleton subtype has cardinality one (`card_subtype_singleton_eq_one`), while there are three labels in total (`DisjointCoordinate.card`). The ratio is therefore $1/3$.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_subtype_singleton_eq_one`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.card`.
