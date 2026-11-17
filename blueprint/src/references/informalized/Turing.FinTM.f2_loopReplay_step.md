<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopReplay_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Replay Step

**Claim.** With active replay control, tape contents $uv$, and head at $|u|$, one step halts with tape $u$ and unchanged output if $v$ is empty; if $v=b::v'$, it remains active, advances the head to $|u|+1$, keeps tape $uv$, and appends $b$ to the output.

**Proof.** The replay transition reads the tape at the head position. The buffer-read fact identifies the symbol there as the head of the remaining suffix (`f2_loopBuffer_read`). If the suffix is empty, no symbol is available: the transition halts, leaves the head fixed, and the tape update removes the empty suffix, leaving $u$; output is unchanged. If the suffix begins with $b$, the transition emits $b$ and advances the tape head by one while leaving the stored tape unchanged. In both cases the input head is stationary (`moveInputPos_zero`), and the resulting fields are precisely those claimed.

**Key facts.** `Turing.FinTM.f2_loopBuffer_read`, `Turing.moveInputPos_zero`.
