<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.scan_const_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant-Word Writer Trace

**Claim.** The constant-word writer follows its forward writing configurations through time $|w|$, then its return configurations through time $2|w|+1$, and thereafter remains in the designated done configuration.

**Proof.** First, the forward configuration at time $0$ is exactly the given initial configuration: the written prefix is empty, the input position is unchanged, and the state hypothesis identifies the initial writing state. The trace theorem for a forward pass, turn, return pass, and stationary endpoint then reduces the claim to checking one transition in each phase (`catalog_trace_run`). For $r<|w|$, the current forward configuration has the writer in phase $r$ and the first $r$ symbols written; its transition writes symbol $w[r]$, advances the selected work-tape head, and enters phase $r+1$. The one-step scanned-write lemma gives precisely the next forward configuration (`scan_write_step`); the input head does not move. At the end of the forward pass, the transition takes the writer into the backward phase at index $|w|$ without moving either head (`step_of_inputMoveAction`). For each $r<|w|$, the return configuration indexed by $r+1$ reads an input position at which the writer moves the work-tape head left and decreases its backward index to $r`; the resulting configuration is the return configuration indexed by $r$ (`step_of_tapeAction_move`). From return index $0$, an input-move transition enters the done state and gives the designated endpoint (`step_of_inputMoveAction`). That endpoint transitions to itself, so all later times have the claimed configuration (`step_of_inputMoveAction`).

**Key facts.** `Turing.catalog_trace_run`, `Turing.scan_write_step`, `Turing.step_of_inputMoveAction`, `Turing.step_of_tapeAction_move`.
