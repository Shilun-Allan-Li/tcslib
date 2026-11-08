<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.hammingSpheres_pairwise_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairwise disjoint Hamming spheres

**Claim.** The Hamming spheres centred at $u$, indexed by the natural numbers below $r$, are pairwise disjoint.

**Proof.** Take any two distinct indices in the stated range. Their corresponding spheres are disjoint by the fact that spheres with the same centre and distinct radii cannot share a word (`hammingSpheres_disjoint`). This is precisely pairwise disjointness of the family.

**Key facts.** `CommunicationComplexity.hammingSpheres_disjoint`.
