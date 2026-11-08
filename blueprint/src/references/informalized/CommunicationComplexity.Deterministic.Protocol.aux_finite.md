<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.aux_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of the Leaf Rectangle Collection

**Claim.** For any protocol and input restrictions $A$ and $B$, the collection of its auxiliary leaf rectangles is finite.

**Proof.** Induct on the protocol. At an output node, the collection consists of the single rectangle $A\times B$, so it is finite. At an Alice node, the collection is the union of the collections for the false and true subprotocols, with the first-input restriction further intersected with the corresponding bit class. Each collection is finite by induction, so their union is finite. At a Bob node the same reasoning applies, with the second-input restriction further intersected with the corresponding bit class.
