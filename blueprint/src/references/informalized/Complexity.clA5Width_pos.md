<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Width_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Snapshot Block Width

**Claim.** For every finite-state binary Turing machine and every binary code for its optional states, the snapshot block width is positive.

**Proof.** The width is the state-code width plus $2+2M.k$. Both summands are natural numbers, and the second is at least $2$. Hence the total width is positive.
