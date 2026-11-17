<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Read Phase

**Claim.** Starting with the machine in its initial read control, one step records whether the cell under tape 0's head is occupied. A second step enters the initial forward scan if it is occupied, and the exit control if it is blank; the other configuration data remain unchanged.

**Proof.** Let $b$ be the Boolean indicating whether the current cell of tape 0 contains a symbol. In the read component machine, the first transition changes the control from the unset bit to the stored bit $b$ and makes no movement or tape modification. The one-step calculation uses the transition rule for an input-move action (`step_of_inputMoveAction`), the zero-step run identity (`runFrom_zero`), and the fact that zero movement fixes the input-head position (`moveInputPos_zero`). The host-machine phase theorem (`phaseHostTM_run`) applies because the redirect is disabled at the initial unset-bit control and sends the stored-bit control to the appropriate phase. If $b$ is true, that phase is the forward scan at index zero with initial accumulator $a_0$; if false, it is the exit phase. This gives the two-step configuration equality, while the phase change itself leaves all non-control data untouched.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`, `Turing.step_of_inputMoveAction`, `Turing.phaseHostTM_run`.
