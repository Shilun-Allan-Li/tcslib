<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamPos_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive clamped positions

**Claim.** For every finite binary string $x$ and offset $i$, moving right from the clamped input-head position for $i$ gives the clamped position for $i+1$.

**Proof.** Separate the cases $i<|x|$ and $i\geq |x|$. In the first case, the clamped position is the interior position $i+1$; it is not at the right boundary. The right-move formula therefore advances it by one, which is the clamped position for $i+1$. In the second case, the clamped position is already the right boundary $|x|+1$. Moving right there leaves it fixed by the boundary rule, and the position for $i+1$ is the same boundary. Thus the positions agree in both cases.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_rightBoundary`.
