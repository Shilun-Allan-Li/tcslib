<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.supportFiber_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint support fibers

**Claim.** For distinct coordinate sets S and T, the support fibers of a fixed word over S and T are disjoint.

**Proof.** Suppose a word v belonged to both fibers. By the definition of a support fiber, the set of coordinates where v differs from the fixed word u would then equal S and also equal T. Hence S = T, contradicting their assumed distinctness. No word can belong to both fibers, which is exactly their disjointness.
