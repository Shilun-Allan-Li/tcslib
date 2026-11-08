<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_clear_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clear-Tape Head Displacement Bound

**Claim.** During the bounded run of the clearing machine from the specified snapshot, every work-tape head remains within distance $|w|+1$ of its position in the original configuration.

**Proof.** The clearing-snapshot result (`recordStep_clear_snapshot`) bounds the destination tape's head throughout the run between its original position minus one and its original position plus $|w|$. Converting this interval bound to an absolute displacement gives at most $|w|+1$. Every other head is stationary in the snapshot and during the clearing machine's run, so its position differs from its original position only by the snapshot's zero displacement; its bound follows as well.

**Key facts.** `Turing.recordStep_clear_snapshot`.
