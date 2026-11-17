<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_disjointCoordinateVector_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity After Disjointness Conditioning

**Claim.** Under the hard distribution conditioned on disjointness, the generated disjoint-coordinate vector is identically distributed to a uniformly drawn coordinate vector.

**Proof.** The joint law of the special coordinate and the generated disjoint-coordinate vector, under the distribution conditioned on disjointness, is the product of the uniform law on special coordinates and the uniform law on coordinate vectors (\texttt{identDistrib\_specialCoordinate\_disjointCoordinateVector\_uniform\_prod}). Project both sides of this identity in distribution onto the second component; identical distributions are preserved by measurable maps. The resulting product marginal is the uniform coordinate-vector law, as stated by \texttt{identDistrib\_uniformProd\_snd\_uniformDisjointCoordinateVector}. Therefore the generated vector has the claimed uniform law.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_uniformProd_snd_uniformDisjointCoordinateVector`.
