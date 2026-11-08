<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepCfg_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Sweep Update

**Claim.** Writing $b$ at the frontier and moving the work head one step right changes the represented frontier from $z$ to $z+1$, moves $b$ onto the left stack, removes the first entry of the right stack, and leaves the input position and output unchanged.

**Proof.** The action enters state $q'$, emits no output, and moves the work head from $z$ to $z+1$. Its input-head movement is zero, so the input position is unchanged (`moveInputPos_zero`). For the work tape, the update that writes $b$ at the old frontier while the right stack begins with $a$ is exactly the new zipper representation with frontier $z+1$, left stack $b::l$, and right stack $r$ (`sweepTape_right`). The head position, state, and output fields then agree as well, giving equality of configurations.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.sweepTape_right`.
