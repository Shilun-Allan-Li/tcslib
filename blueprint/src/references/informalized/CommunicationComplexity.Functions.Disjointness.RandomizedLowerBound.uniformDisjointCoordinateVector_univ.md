<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total mass of the uniform vector law

**Claim.** The uniform law on length-$n$ disjoint-coordinate vectors assigns mass one to the set of all such vectors.

**Proof.** Apply the subset-measure formula from `uniformDisjointCoordinateVector_real` to the whole space. The subtype of vectors belonging to the whole space has the same cardinality as the space itself, namely $3^n$. The resulting ratio is $3^n/3^n=1$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_real`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.card`.
