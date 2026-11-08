<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitCount_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step counting simulation

**Claim.** Applying the transformed counting action to the counting-host configuration associated with a source configuration yields exactly the counting-host configuration associated with the source configuration after applying the original action.

**Proof.** Separate the cases according to whether the source action emits an output bit. If it emits none, the host makes no input movement, leaving its encoded output count and saturated input position unchanged. The overflow flag therefore stays the same, the source work-tape actions are copied to the host's successor-indexed tapes, and the extra tape storing $s$ is untouched. Zero input movement preserves the saturated position (`moveInputPos_zero`). If the source action emits a bit, the host moves its input head one place to the right, thereby advancing the encoded count by one; the new overflow flag is the old overflow flag or the fact that the previous scan was blank. By the overflow update identity (`splitCount_over`), this is exactly the overflow test for the advanced count. The position after moving right is the saturated position for that count (`splitPos_succ`). In both cases the state map records the source successor, or the return state if the source action halts, with the updated overflow flag. The work tapes and their head positions match those obtained from applying the original action, and neither host action adds output. Thus all components agree with the counting-host configuration formed from the source successor.

**Key facts.** `Turing.FinTM.splitCount_over`, `Turing.moveInputPos_zero`, `Turing.FinTM.splitPos_succ`.
