<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.hammingSphere_eq_biUnion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hamming spheres as support-fiber unions

**Claim.** The sphere of radius $r$ centred at $u$ is the union, over all coordinate subsets of size $r$, of the words whose differing coordinates from $u$ are exactly that subset.

**Proof.** For any word $v$, its support relative to $u$ is the set of coordinates where $v$ differs from $u$. By the definition of Hamming distance, the size of this support is $d(u,v)$. Thus if $v$ lies on the sphere of radius $r$, its support is an $r$-element subset of the coordinate positions, and $v$ belongs to the fiber indexed by that support. Conversely, membership in a fiber indexed by an $r$-element subset means the support has size $r$, so the Hamming distance is $r$ and $v$ lies on the sphere.
