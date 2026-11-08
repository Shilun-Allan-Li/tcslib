<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_measure_condBit_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive mass of conditioning-bit events

**Claim.** Every event fixing one of Alice's conditioning bits to either Boolean value has positive probability.

**Proof.** Construct a vector that is neither at every coordinate except $k$, where the symbol is chosen so that the conditioning bit at $k$ equals $b$; the coordinate specification guarantees this value (`coordinateWithCondBit_spec`). Thus the event contains this vector as a singleton. That singleton has real mass $1/3^n$ (`uniformDisjointCoordinateVector_singleton`), which is positive. Monotonicity of measure then shows the event has positive real mass, and hence positive measure.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateWithCondBit_spec`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_singleton`.
