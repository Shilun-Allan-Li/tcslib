<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.control_step' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Control Transition

**Claim.** If every transition from state $q$ moves the input head by $m$, leaves the work tapes and their heads unchanged, emits nothing, and enters state $r$, then a configuration in state $q$ takes one step to the configuration with state $r$ and input head moved by $m$, with all other components unchanged.

**Proof.** Since the configuration has state $q$, the definition of one step identifies its successor with the result of applying the transition at $q$ to that configuration. The hypothesis makes this transition the control action that moves the input head by $m$, enters $r$, and makes no work-tape changes or output. Applying it therefore gives exactly the stated configuration; equality follows by comparing the configuration components.
