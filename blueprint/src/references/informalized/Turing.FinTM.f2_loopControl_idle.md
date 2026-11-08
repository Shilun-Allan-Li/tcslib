<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopControl_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle Loop Control Action

**Claim.** A loop-control action with no work-tape writes or movements and no emitted output is the control action with the same input movement and next state.

**Proof.** The two actions have the same input movement and next state. On every work tape, the specified write is absent and the movement is zero, and both actions emit no output. Thus all components of the actions agree.
