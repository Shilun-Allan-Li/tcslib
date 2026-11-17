<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean :: CommunicationComplexity.Deterministic.Protocol.mem_leafRectanglesFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the leaf rectangle finset

**Claim.** A set $R$ belongs to the finite set enumerating a protocol's leaf rectangles if and only if it is a leaf rectangle of that protocol.

**Proof.** The finite set is obtained by converting the finite set of leaf rectangles to a finset. Membership in the finset conversion of a finite set is equivalent to membership in the original set. Applying this fact to the collection of leaf rectangles gives the stated equivalence.
