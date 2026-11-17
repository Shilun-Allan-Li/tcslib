<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialCoordinateEvent_inter_specialIntersect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed Intersecting Special Coordinate

**Claim.** For any fixed coordinate $i$, the probability that the special coordinate is $i$ and both special bits are true is $1/(4n)$.

**Proof.** Describe the event as the product condition that $T$ lies in the singleton $\{i\}$, that each special bit lies in $\{\mathrm{true}\}$, and that the other-coordinate vector is unrestricted. The product-measure formula for hard samples (`hardSample_measureReal_fieldProduct`) expresses its probability as the product of the corresponding probabilities in each component. The uniform law on $\mathrm{Fin}(n)$ assigns $1/n$ to a singleton (`uniformFin_singleton`); each uniform Boolean bit assigns $1/2$ to a singleton (`uniformBool_singleton`); and the unrestricted other-coordinate vector has probability $1$ (`uniformDisjointCoordinateVector_univ`). Multiplying gives $(1/n)(1/2)(1/2)(1)=1/(4n)$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.hardSample_measureReal_fieldProduct`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_univ`.
