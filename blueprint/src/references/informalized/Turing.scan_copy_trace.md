<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.scan_copy_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Copy Machine Trace

**Claim.** Starting in the sweep state with the input head at position $1$, the input-copy machine follows its forward scan through time $|x|$, its return scan through time $2|x|+1$, and then stays in the designated done configuration.

**Proof.** At time $0$, the forward configuration is the initial one: its input head is at position $1$, no prefix has yet been copied, and its state is the sweep state. Apply the general theorem for a forward pass, a turn, a return pass, and a stationary endpoint (`catalog_trace_run`). During the forward pass, at index $r<|x|$, the input head reads $x[r]$ (`inputSymbolInner`). The machine writes that symbol to the selected work tape, moves both heads right, and remains in the sweep state; the scanned-write lemma identifies the resulting configuration with the forward configuration at index $r+1$ (`scan_write_step`). At the right boundary the input symbol is absent, so the transition enters rewind, moves the input head left, and places the work-tape head at the endpoint prescribed for the return configurations (`step_of_tapeAction_move`). At return index $r+1$, the input head reads $x[r]$; the rewind transition moves left and yields return index $r` (`inputSymbolInner`, `step_of_tapeAction_move`). At return index $0$, the input symbol is absent and the machine moves the input head right into the done state, producing the designated endpoint (`step_of_tapeAction_move`). The done state has a stationary transition, so the endpoint persists thereafter (`step_of_inputMoveAction`). The input-head position calculations in these steps use the stated formulas for moving left and right (`Turing.FinTM.moveInputPos_neg_val`, `moveInputPos_pos_of_ne_right`).

**Key facts.** `Turing.catalog_trace_run`, `Turing.inputSymbolInner`, `Turing.scan_write_step`, `Turing.step_of_tapeAction_move`, `Turing.step_of_inputMoveAction`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.moveInputPos_pos_of_ne_right`.
