<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.MultiTapeTM.inputPos_runFrom_of_inputTape_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary Input Head

**Claim.** If every transition prescribes zero movement of the input head, then from any configuration the input-head position remains unchanged after every number of steps.

**Proof.** For a single step, consider whether the configuration is already halted. If so, the machine leaves it unchanged. Otherwise its transition prescribes zero input-head movement, so applying that transition leaves the input-head position unchanged. Thus the input-head-position function is preserved by one application of the machine's step map. Iterating a map that preserves this function preserves it after any number $t$ of steps, giving the claimed equality.
