<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_remaining_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step characterization of remaining product bits

**Claim.** For $j<|a|+|b|$, the remaining-bit conditions from position $j$ onward are equivalent to the required bit equation at $j$ together with the remaining-bit conditions from position $j+1$ onward.

**Proof.** In the forward direction, the condition for all positions at least $j$ gives the bit equation at $j$ directly. The length bound and terminal carry condition are unchanged, and every position at least $j+1$ is also at least $j$, so the remaining conditions follow. Conversely, assume the equation at $j$ and the remaining conditions from $j+1$ onward. To establish the condition at any position $i$ in the required range, split into $i=j$ and $i\ne j$. In the first case use the assumed equation; in the second, the lower bound $j\le i$ and inequality $i\ne j$ imply $j+1\le i$, so the later-position conditions apply.
