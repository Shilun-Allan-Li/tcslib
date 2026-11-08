<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.workChain_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Chain Vanishes to the Left

**Claim.** If $t\le T$, then at position $-T-1$ the work-chain value after $t$ steps is none for every work tape.

**Proof.** The work-tape head's absolute position after $t$ steps is at most $t$ (`Complexity.abs_workTapePos_le`). Hence its position is at least $-t$, and since $t\le T$, it is at least $-T$. In particular, the head is strictly to the right of $-T-1$. The work-chain is defined to be none at positions strictly left of the head, so its value at $-T-1$ is none.

**Key facts.** `Complexity.abs_workTapePos_le`.
