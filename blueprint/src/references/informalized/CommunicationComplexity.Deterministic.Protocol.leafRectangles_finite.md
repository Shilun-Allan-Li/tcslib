<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.leafRectangles_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of leaf rectangles

**Claim.** For every deterministic two-party protocol, its collection of leaf rectangles is finite.

**Proof.** Apply the auxiliary finiteness result (`aux_finite`) to the protocol with both initial input sets equal to the full spaces $X$ and $Y$. By definition, the auxiliary collection for these initial sets is exactly the protocol's collection of leaf rectangles, so that collection is finite.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.aux_finite`.
