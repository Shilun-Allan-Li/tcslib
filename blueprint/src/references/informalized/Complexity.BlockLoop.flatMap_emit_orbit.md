<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.flatMap_emit_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit Emission Over a Finite Range

**Claim.** Under the orbit and nonemptiness hypotheses, concatenating emissions at iterates indexed from $0$ through $N-1$ gives exactly $out$ applied to the encoding of $P(K)$ and the encoding of the empty string with $Q(K)$.

**Proof.** First use the finite-range single-emission principle ($flatMap_range_eq_single$): since $K<N$, it suffices to show that every emission in the range is empty except at index $K$, where it is the claimed output. Fix $i<N$ and split into the three possibilities $i<K$, $i=K$, or $K<i$. If $i<K$, the orbit hypothesis gives the prescribed nested encoding, with a nonempty string of $K-i$ ones in its second component. Since $P(i)$ is also nonempty, the emission rule returns the empty list. At $i=K$, the orbit is encoded using $P(K)$ and a zero-length string of ones; thus the second component's first projection is empty, while $P(K)$ is nonempty, so the emission is exactly $out$ of that state. If $K<i$, the completed-state hypothesis says the iterate is $blockDone$, whose first projection is empty, and hence its emission is empty. Therefore only index $K$ contributes, with the asserted value.

**Key facts.** `Complexity.flatMap_range_eq_single`.
