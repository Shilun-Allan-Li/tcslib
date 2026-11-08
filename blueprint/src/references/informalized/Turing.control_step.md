<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.control_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Control-Only Transition

**Claim.** If every transition from state $q$ moves no head, changes no tape contents, emits no output, and enters state $r$, then one step from any configuration in state $q$ changes only its state to $r$.

**Proof.** Because the configuration's state is $q$, one machine step applies the transition specified for $q$, evaluated at the configuration's current input and work-tape symbols. By hypothesis this transition is the control-only action with zero input movement and next state $r$. Applying that action leaves the input-head position fixed, leaves every work tape and work-tape head fixed, and appends no output. Its state component is $r$, so the resulting configuration is exactly the original one with its state changed to $r$.
