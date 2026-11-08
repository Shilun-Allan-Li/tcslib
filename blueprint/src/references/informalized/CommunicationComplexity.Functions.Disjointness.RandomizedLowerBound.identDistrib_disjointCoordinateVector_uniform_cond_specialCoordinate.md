<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_disjointCoordinateVector_uniform_cond_specialCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Uniformity at a Fixed Coordinate

**Claim.** Conditioned on disjointness and on the special coordinate being $i$, the generated disjoint-coordinate vector is identically distributed to a uniformly drawn coordinate vector.

**Proof.** The joint law of the special coordinate and the generated vector under disjointness conditioning is the product of their uniform laws (\texttt{identDistrib\_specialCoordinate\_disjointCoordinateVector\_uniform\_prod}). Reorder the pair so the vector is first and the special coordinate second; the resulting sample is therefore identically distributed to the reversed pair under that product law. Now condition both sides on the second component belonging to $\{i\}$. The conditional-distribution principle for identically distributed pairs gives equality in distribution of the first components under the corresponding conditional measures (\texttt{ProbabilityTheory.IdentDistrib.cond\_of\_pair}). On the product side, conditioning the uniform product on its first coordinate being $i$ leaves the second component uniform, by \texttt{identDistrib\_uniformProd\_snd\_uniformDisjointCoordinateVector\_cond\_fst}. Combining these identities yields the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_specialCoordinate_disjointCoordinateVector_uniform_prod`, `ProbabilityTheory.IdentDistrib.cond_of_pair`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_uniformProd_snd_uniformDisjointCoordinateVector_cond_fst`.
