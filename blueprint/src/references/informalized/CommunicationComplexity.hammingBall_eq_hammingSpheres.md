<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.hammingBall_eq_hammingSpheres -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hamming balls as unions of spheres

**Claim.** The Hamming ball of radius $r$ centred at $u$ is the disjoint union of the Hamming spheres centred at $u$ with radii from $0$ through $r$.

**Proof.** A word $v$ lies in the ball exactly when its Hamming distance $d(u,v)$ is at most $r$. If it lies in the ball, choose $k=d(u,v)$. Then $k$ belongs to the range from $0$ through $r$, and $v$ lies on the sphere of radius $k$. Conversely, membership in one of those spheres says $d(u,v)=k$ for some $k\le r$, so $v$ lies in the ball. The spheres are pairwise disjoint by `hammingSpheres_pairwise_disjoint`, since a word cannot have two distinct distances from the same centre; thus the union is disjoint.

**Key facts.** `CommunicationComplexity.hammingSpheres_pairwise_disjoint`.
