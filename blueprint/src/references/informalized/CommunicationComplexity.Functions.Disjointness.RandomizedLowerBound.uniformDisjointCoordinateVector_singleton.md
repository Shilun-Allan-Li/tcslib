<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of a single vector

**Claim.** Every individual length-$n$ disjoint-coordinate vector has uniform mass $1/3^n$.

**Proof.** For the uniform law on a finite nonempty discrete space, the measure of a subset is its cardinality divided by the cardinality of the whole space (`uniformOn_univ_measureReal_eq_card_subtype`). The subtype of vectors in the singleton set containing the given vector has cardinality one (`card_subtype_singleton_eq_one`). The full function space has cardinality $3^n$, since there are three choices at each of the $n$ coordinates (`DisjointCoordinate.card`). Thus the singleton's measure is $1/3^n.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_subtype_singleton_eq_one`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.card`.
