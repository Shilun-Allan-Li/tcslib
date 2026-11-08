<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.step_of_tapeAction_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step from a Tape Movement Action

**Claim.** If the transition from state $q$ is the specified movement action on tape $i$, then one step enters state $q'$, moves the input head by $\mathrm{inp}$, and changes tape $i$'s head position by $m$, leaving the other configuration data unchanged.

**Proof.** The state hypothesis makes the step apply the transition for $q$, and the transition hypothesis identifies it with the stated tape action. Applying that action moves the input head by $\mathrm{inp}$ and changes each work-head position by its prescribed movement: tape $i$ moves by $m$, while every other tape has movement zero. There are no writes or output, so tape contents and output are unchanged; the action also sets the state to $q'$. These componentwise updates are precisely the claimed configuration.
