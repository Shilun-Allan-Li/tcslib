<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/PairwiseIndependence.lean :: FABL.pairwiseIndependentColumn_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Nonzero-Vector Enumeration

**Claim.** When $n\le 2^\ell-1$, the map assigning to each index its enumerated nonzero vector in $\mathbb F_2^\ell$ is injective.

**Proof.** The assignment is the composite of three maps: the inclusion of the first $n$ indices into the full index set, the bijection from that full index set to the nonzero vectors, and the map forgetting the subtype proof that a vector is nonzero. The inclusion is injective, the bijection is injective, and forgetting a subtype proof preserves injectivity because equal underlying vectors give equal subtype elements. A composite of injective maps is injective.
