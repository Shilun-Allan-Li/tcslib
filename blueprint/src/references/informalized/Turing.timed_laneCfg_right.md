<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_laneCfg_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right-Moving Zipper Step

**Claim.** Applying the specified write-and-move action to the zipper configuration yields the zipper configuration with frontier advanced by one, the written symbol prepended to the left list, and the right list advanced past its head.

**Proof.** Compare the configuration fields. The action enters state $q'$, leaves the input position fixed because its input-head movement is zero (`Turing.moveInputPos_zero`), and leaves the output unchanged because it emits no symbol. On the selected lane, it writes $b$ at the old frontier $z$ and moves that lane’s head one cell right. The sweep-tape update identity (`Turing.FinTM.sweepTape_right`) identifies the resulting tape with the zipper at frontier $z+1$, left list $b::l$, and right list $r$. Every other lane’s tape and head position is unchanged by the action, so all fields agree with the claimed configuration.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.sweepTape_right`.
