<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.moveInputPos_neg_one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leftward Input Head Bound

**Claim.** For every $n\in\mathbb{N}$ and every input-head position among the $n+2$ positions, moving the head one position left with the clamped rule gives a position at most $n$.

**Proof.** Split according to whether the position is the left boundary. At position zero, the left-boundary rule (`moveInputPos_leftBoundary`) fixes the position at zero, which is at most $n$. At any nonzero position, the left-movement rule (`moveInputPos_neg_of_ne_left`) gives the new value as $p-1$. Since $p$ is a position in the $n+2$-element range, $p<n+2$; and since it is nonzero, $p-1\le n$.

**Key facts.** `Turing.moveInputPos_leftBoundary`, `Turing.moveInputPos_neg_of_ne_left`.
