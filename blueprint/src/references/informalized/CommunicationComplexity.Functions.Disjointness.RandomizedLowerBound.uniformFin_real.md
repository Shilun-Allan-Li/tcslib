<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_real -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform probability of a finite subset

**Claim.** For a subset $S$ of $	ext{Fin }n$, the uniform law assigns probability equal to the number of its elements divided by $n$.

**Proof.** The uniform-measure formula `uniformOn_univ_measureReal_eq_card_subtype` expresses the measure of $S$ as the cardinality of the subtype of its elements divided by the cardinality of the ambient space. The ambient space $	ext{Fin }n$ has cardinality $n$, giving the claimed expression.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`.
