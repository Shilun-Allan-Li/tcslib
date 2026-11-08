<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.workChain_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Boundary Work Chain

**Claim.** For every work tape, if $t\le T$, the work-chain value at position $T$ after $t$ steps equals the symbol scanned by that tape at time $t$.

**Proof.** The work-tape head position has absolute value at most the number of steps taken, by the head-displacement bound (`Complexity.abs_workTapePos_le`). Thus its position is at most $t$, and hence at most $T$. The condition defining the work-chain value at $T$ is therefore true, so that value is exactly the scanned symbol.

**Key facts.** `Complexity.abs_workTapePos_le`.
