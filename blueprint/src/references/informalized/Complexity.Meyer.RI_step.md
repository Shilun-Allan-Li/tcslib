<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.RI_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Read After One Step

**Claim.** After one machine step, the input read at offset $d$ follows the stated update rule: a halted configuration retains the read at $d$; for an active configuration, it retains that read when both the current read and the read at the attempted movement are absent, and otherwise reads at the shifted offset.

**Proof.** First split according to whether the configuration is halted. In the halted case, a step leaves the configuration unchanged, so its input read at offset $d$ is unchanged; this is exactly the halted branch of the update rule (`Turing.MultiTapeTM.step_of_halt`).

Now suppose the configuration is active, in state $q$. Its step is the transition prescribed by the machine from the symbols currently read, applied to the configuration (`Complexity.Meyer.step_eq`). Let $m$ be the input-head movement prescribed by that transition. The new read at offset $d$ is the extended input lookup at the new head position plus $d$. Consider the three possible movements.

For zero movement the head does not change, and the update rule returns the read at $d$. For a positive movement, if the head is already at the right boundary, movement is clamped there; both the current read and the read at the attempted movement are absent, so the rule returns the read at $d$. Away from that boundary, the head moves one position right (`Turing.moveInputPos_pos_of_ne_right`). If both reads tested by the rule are absent, the input must be empty, and the resulting read is absent as well. Otherwise the resulting lookup is precisely the read at offset $d+m$. The characterization of absent extended lookups (`Complexity.Meyer.xhat_eq_none`) justifies these boundary and empty-input conclusions.

For a negative movement, the left boundary is handled in the same way: at position zero the head stays there (`Turing.moveInputPos_leftBoundary`), and both reads in the rule are absent. Away from that boundary, the head moves one position left (`Turing.moveInputPos_neg_of_ne_left`). If both tested reads are absent, the input is empty and the resulting read is absent; otherwise the resulting lookup is the read at offset $d+m$. This again uses the characterization of absent extended lookups (`Complexity.Meyer.xhat_eq_none`). These cases establish the update rule in all situations.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Complexity.Meyer.step_eq`, `Complexity.Meyer.xhat_eq_none`, `Turing.moveInputPos_rightBoundary`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_leftBoundary`, `Turing.moveInputPos_neg_of_ne_left`.
