<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopControl_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle Controller Actions

**Claim.** When the flag, counter, and payload instructions all specify no write or movement and no bit is emitted, the controller action is just the input-only action with the given direction and successor state.

**Proof.** At each work-tape index, the controller either selects one of the three distinguished tapes or falls through to the default. In each case the selected instruction is no write and zero movement. The action therefore has no work-tape effects; it also emits nothing, keeps the given input direction, and has the specified successor state. This is exactly the input-only action.
