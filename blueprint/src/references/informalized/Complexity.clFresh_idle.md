<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFresh_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationarity of the completed control

**Claim.** Every configuration of the unrestricted field loader on input $x$ whose state is the completed reading control is unchanged after one step.

**Proof.** In the completed control, the transition is the control-only action that keeps the state fixed and makes no work-tape changes, emits no output, and requests zero movement on the input head. The control-action formula (`Turing.FinTM.controlAction_apply`) therefore reduces the step to a configuration update that can only replace the state and input position. The state is already the required one, and zero movement leaves the input-head position unchanged (`Turing.moveInputPos_zero`). Thus all components of the configuration agree with their original values.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
