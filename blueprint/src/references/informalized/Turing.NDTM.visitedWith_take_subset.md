<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.visitedWith_take_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Positions on a Prefix

**Claim.** Every head position visited on a chosen work tape during the run under the prefix of $w$ of length $j$ is also visited during the run under $w$.

**Proof.** A position in the visited set for $w.take\ j$ is represented by some index $n$ in the range from $0$ through $|w.take\ j|$. This means $n\le \min(j,|w|)$. In particular, $n\le |w|$, so $n$ is a valid index for the visited set of $w$. The prefix of $w.take\ j$ of length $n$ equals the prefix of $w$ of length $n$, since $n\le j$. Therefore the same index gives the same head position and witnesses membership in the larger visited set.
