<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRound_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round at a Clause Marker

**Claim.** When the unconsumed input begins with the marker bit $1$ and the phase is $0$, one round emits $[1]$, consumes that bit, leaves the fresh cursor fixed, and enters phase $1$.

**Proof.** Dropping the consumed prefix $p$ leaves a list beginning with $1$. In phase $0$, the round treats this leading bit as a clause marker: it emits $[1]$, increases the consumed length from $|p|$ to $|p|+1$, leaves the fresh cursor at $j$, and changes the phase to $1$.
