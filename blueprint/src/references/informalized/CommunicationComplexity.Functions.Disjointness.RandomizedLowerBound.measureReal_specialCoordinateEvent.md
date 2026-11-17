<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialCoordinateEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Law of the Special Coordinate

**Claim.** For any fixed coordinate $i$, the event that the special coordinate $T$ equals $i$ has probability $1/n$.

**Proof.** Write the event as the product restriction that $T$ lies in $\{i\}$ while both special bits and the vector of other-coordinate labels are unrestricted. The hard-sample product-measure formula gives the product of these four marginal masses (`hardSample_measureReal_fieldProduct`). The singleton has uniform mass $1/n$ (`uniformFin_singleton`), and each unrestricted factor has mass $1$ (`uniformBool_univ` and `uniformDisjointCoordinateVector_univ`). The product is therefore $1/n$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.hardSample_measureReal_fieldProduct`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_univ`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_univ`.
