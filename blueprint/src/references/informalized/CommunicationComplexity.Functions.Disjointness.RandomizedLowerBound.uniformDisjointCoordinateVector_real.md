<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_real -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform measure of a subset

**Claim.** For a set $S$ of length-$n$ disjoint-coordinate vectors, its uniform measure is the number of vectors in $S$ divided by $3^n$.

**Proof.** The uniform measure of a subset of a finite nonempty discrete space is its cardinality divided by the cardinality of the whole space (the uniform-measure formula `uniformOn_univ_measureReal_eq_card_subtype`). Here the whole space is the function space from $n$ coordinates to the three disjoint-coordinate labels, whose cardinality is $3^n$: a function space over a finite index set has cardinality equal to the coordinate cardinality raised to the index cardinality, and `DisjointCoordinate.card` gives three choices per coordinate. Substituting this ambient cardinality yields the stated ratio.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.card`.
