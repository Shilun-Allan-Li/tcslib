<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity and independence of the coordinates

**Claim.** Under the hard-sample law conditioned on disjoint inputs, the special coordinate and the disjoint-coordinate vector have the product of their respective uniform laws.

**Proof.** To identify the two laws, it suffices to compare their masses on singleton pairs $(i,c)$, since the spaces are finite and discrete. The preimage of $(i,c)$ under the map sending a sample to its special coordinate and coordinate vector is the intersection of the events that the special coordinate is $i$ and the vector is $c$. Its conditional mass is $1/(n\,3^n)$, by the fiber-mass formula (`disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber`). Under the product law, the singleton mass is the product of the two singleton masses: the uniform special-coordinate mass is $1/n$ (`uniformFin_singleton`), and the uniform vector mass is $1/3^n$ (`uniformDisjointCoordinateVector_singleton`). This product is also $1/(n\,3^n)$, so the singleton masses, and hence the laws, agree.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialCoordinate_disjointCoordinateVector_fiber`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_singleton`.
