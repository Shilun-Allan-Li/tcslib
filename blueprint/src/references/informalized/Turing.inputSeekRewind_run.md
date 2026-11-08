<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: Turing.inputSeekRewind_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Seek and Rewind Run

**Claim.** Starting in state start, the input-seek-and-rewind machine reaches done with its input head at zero by a time at most the initial input-head position plus three; it is not done earlier, and neither work-tape head moves during this run.

**Proof.** Apply the general rewind result (`Turing.FinTM.rewind_heads`) to the machine's start and scan transitions. It supplies a time $r$ at which the machine is in the intermediate left state with input position $1$, with $r\le p(d)+2$, and shows that both work-tape heads have remained fixed through that time.

At any $u\le r$, the machine cannot already be done. Indeed, if it were, its done-state transition would leave that configuration fixed. The run composition law (`Turing.MultiTapeTM.runFrom_add`) and iteration at a fixed point would then force the configuration at time $r$ to equal the one at time $u$, contradicting that the former is in the left state and the latter is done. Thus done is not reached before $r+1$.

The next transition is the control action that moves left and enters done. The one-step transition rule (`Turing.step_of_inputMoveAction`) and the control-action configuration formula (`Turing.FinTM.controlAction_apply`) show that this changes the state and moves the input head from position $1$ to position $0$, using the value formula for a left move (`Turing.FinTM.moveInputPos_neg_val`). Set the completion time to $r+1$. It is at most $p(d)+3$, and both work heads still agree with their initial positions: they are fixed through time $r$, and the final control action does not move them.

**Key facts.** `Turing.FinTM.rewind_heads`, `Turing.MultiTapeTM.runFrom_add`, `Turing.step_of_inputMoveAction`, `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`.
