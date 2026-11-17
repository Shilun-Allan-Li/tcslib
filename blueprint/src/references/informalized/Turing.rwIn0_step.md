<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.rwIn0_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Input Rewind Step

**Claim.** From the initial input-rewind state with the input head at position $|x|+1$, the machine moves the input head left once to position $|x|$ and leaves the other configuration data unchanged.

**Proof.** In state $\mathrm{rwInput0}$, the transition is the control action that moves the input head one cell left, enters $\mathrm{rwInput}$, and makes no work-tape move or write and emits no output. The control-action step rule (`Turing.control_step'`) therefore gives the desired successor except for its input position. Since the starting position $|x|+1$ is nonzero, the left-move formula (`Turing.moveInputPos_neg_of_ne_left`) identifies the new position as $(|x|+1)-1=|x|$.

**Key facts.** `Turing.control_step'`, `Turing.moveInputPos_neg_of_ne_left`.
