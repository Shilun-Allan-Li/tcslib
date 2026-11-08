<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecord_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorbing completed recorder state

**Claim.** If a recording-machine configuration is in the completed return state, one step leaves the entire configuration unchanged.

**Proof.** In the completed return state, the recorder transition is a control action that keeps the same state and requests zero movement. Its placed version has the same effect: the placement changes only which tapes receive actions, and every tape receives no write and zero movement (`Complexity.clPlacedAction_eq`). Applying this action therefore preserves the control state and input-head position; all work tapes, work-head positions, and the output are unchanged as well. The zero-movement identity (`Turing.moveInputPos_zero`) confirms that the input-head position is unchanged, so the resulting configuration equals the original one.

**Key facts.** `Complexity.clPlacedAction_eq`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
