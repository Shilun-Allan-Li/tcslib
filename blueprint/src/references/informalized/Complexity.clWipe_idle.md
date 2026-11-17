<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clWipe_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completed Reset Is Stationary

**Claim.** Every configuration of the reset machine in control state $2$ is unchanged by one step.

**Proof.** In control state $2$, the reset machine's control action has zero head movement and leaves the control state at $2$. The control-action application law says its effect on a configuration is to update only the control state and input-head position (`Turing.FinTM.controlAction_apply`). A zero input-head move fixes that position (`Turing.moveInputPos_zero`), so the configuration is unchanged in every field.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
