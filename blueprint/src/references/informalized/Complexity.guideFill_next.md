<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.guideFill_next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adding one filled cell

**Claim.** For either direction, updating the tape filled through $j$ cells at the next coordinate in that direction with its guide mark gives the tape filled through $j+1$ cells.

**Proof.** Compare both sides at an arbitrary coordinate $z$. If $z$ is the newly allocated coordinate, the update assigns exactly its guide mark, which is the value prescribed by filling through $j+1$. At any other coordinate the update leaves the old value unchanged. The interval defining the filled cells through $j+1$ consists of the old interval through $j$ together with precisely this new endpoint, so the old tape already has the required value there and elsewhere remains the original guide tape. This reasoning applies in the rightward direction at $j$ and in the leftward direction at $-j$.
