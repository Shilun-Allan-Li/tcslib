<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/StablePass.lean :: Light.IsStablePass.perm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation from a Stable Pass

**Claim.** If a stable pass places each entry of the input list at its prescribed position and preserves the list length, then the output is a permutation of the input.

**Proof.** Let $N$ be the common length. For each position $j<N$, send $j$ to the position assigned to the input entry there. The prescribed position lies below $N$ (`sortPos_lt`). Moreover, distinct input positions have distinct assigned positions: equality of two assigned positions implies equality of the original positions (`eq_of_sortPos_eq`). Thus this map is an injection from the finite set of $N$ positions to itself, hence a permutation, say $\sigma$.

Represent each list by its values at all positions. The placement condition says that the input value at position $j$ equals the output value at $\sigma(j)$. Consequently the input list is obtained by composing the output's position-value function with $\sigma$. Reindexing a finite list by a permutation does not change its permutation class, so the two lists are permutations of one another.

**Key facts.** `Light.sortPos_lt`, `Light.eq_of_sortPos_eq`.
