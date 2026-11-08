<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.blockCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for a Block Count

**Claim.** For natural numbers $q,K$, a predicate $B$ on finite bit strings, and a finite bit string $l$, the number of the first $K$ consecutive length-$q$ blocks satisfying $B$ is at most $K$.

**Proof.** The count of indices in the range from $0$ to $K-1$ satisfying any predicate is at most the length of that range. The range has length $K$, so the block count is at most $K$.
