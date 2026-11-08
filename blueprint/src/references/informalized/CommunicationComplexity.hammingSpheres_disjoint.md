<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.hammingSpheres_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint spheres at distinct radii

**Claim.** Two Hamming spheres with the same centre and distinct radii are disjoint.

**Proof.** A word in the intersection would have Hamming distance from the centre equal to both radii. Equality of those two distances would force the radii to be equal, contrary to the hypothesis. Therefore the intersection is empty.
