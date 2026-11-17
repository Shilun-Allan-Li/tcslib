<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.step_of_tapeAction_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step from a Tape Write Action

**Claim.** If the transition from state $q$ is the specified write action on tape $i$, then one step enters state $q'$, moves the input head by $\mathrm{inp}$, writes $s$ at tape $i$'s scanned cell, and moves that tape's head by $m$, leaving all other components unchanged.

**Proof.** The state hypothesis selects the transition for $q$, and the transition hypothesis identifies it with the given write action. Applying it moves the input head by $\mathrm{inp}$, writes $s$ at the current position of tape $i$, and increases that tape's head position by $m$. Every other tape has no write and zero movement, and the action emits no output. Its successor state is $q'$, so these component updates give exactly the asserted configuration.
