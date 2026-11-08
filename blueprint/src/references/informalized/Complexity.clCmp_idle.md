<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completed Configurations Are Fixed

**Claim.** If a comparator configuration has completed control carrying Boolean value $b$, one comparator step leaves the entire configuration unchanged.

**Proof.** In completed control, the comparator's transition is the control action that preserves the state, makes no changes to work tapes, and requests zero movement. Applying that action leaves the configuration unchanged: zero input-head movement preserves the input position (`Turing.moveInputPos_zero`), and the other configuration components are unchanged by the control action (`Turing.FinTM.controlAction_apply`).

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
