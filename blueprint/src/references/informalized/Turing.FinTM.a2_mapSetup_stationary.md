<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapSetup_stationary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary non-forward simulation

**Claim.** In non-forward mode, a configuration whose state represents a simulated state remains exactly unchanged after any number of steps.

**Proof.** Write the state of the configuration as a simulated state $q$ paired with a tag. In non-forward mode, the transition from such a state is a control action that keeps that state and makes no work-tape, output, or input-head movement. The control-action application rule (`Turing.FinTM.controlAction_apply`), together with the fact that zero movement leaves the input-head position fixed (`Turing.moveInputPos_zero`), shows that one step returns the original configuration. Induct on the number of steps: time zero is immediate, and at each successor time the run is one step from the preceding configuration (`Turing.MultiTapeTM.runFrom_succ_eq_step'`); the induction hypothesis and the one-step identity give the result.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
