<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_eq_card_subtype_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Measure as a Cardinality Ratio

**Claim.** For every subset $S$ of the finite hard-sample space, its uniform measure is the cardinality of the subtype of samples in $S$ divided by the cardinality of the whole space.

**Proof.** The hard-sample measure is uniform, so the mass of $S$ is the number of points in $S$ divided by the total number of points. The uniform-measure formula first expresses this using the cardinality of the finite set of points satisfying membership in $S$ (`uniformOn_univ_measureReal_eq_card_filter`). That set has the same cardinality as the subtype $\{\omega\mid \omega\in S\}$, yielding the stated ratio.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_filter`.
