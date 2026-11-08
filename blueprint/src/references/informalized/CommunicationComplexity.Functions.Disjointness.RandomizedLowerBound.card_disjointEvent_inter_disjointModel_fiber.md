<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_disjointEvent_inter_disjointModel_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton disjoint-model fibers

**Claim.** For every model value, exactly one hard-sample point both generates disjoint input sets and has that model value.

**Proof.** The set of hard samples satisfying disjointness and mapping to the specified model value is equivalent to the one-element type, by the reconstruction equivalence `disjointEventInterDisjointModelEquiv`. The model records the special coordinate, the generated coordinate labels, and the otherwise ignored label at the special coordinate. Disjointness forces the special bits to be the unique disjoint pair compatible with the recorded generated label; away from the special coordinate, the labels determine the sample’s other coordinates. Thus the sample is uniquely reconstructed. Equivalent finite types have equal cardinality, and the one-element type has cardinality $1$.
