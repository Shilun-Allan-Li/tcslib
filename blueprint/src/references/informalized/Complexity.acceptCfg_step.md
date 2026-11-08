<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.acceptCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility of Machine Steps with the Configuration Map

**Claim.** One step of the halting recognizer from the configuration corresponding to $C$ equals the configuration corresponding to one step of the original machine from $C$.

**Proof.** Split according to whether the original configuration is already halted. If it is halted, its own machine step leaves it unchanged (`Turing.MultiTapeTM.step_of_halt`). When the stored last output bit is false, the transformed machine is in its looping halting state and likewise leaves the corresponding configuration fixed (`Complexity.acceptTM_loop`); when the bit is true, its transformed state is already halted, so its step fixes the configuration as well (`Turing.MultiTapeTM.step_of_halt`).

If the original configuration has state $q$, the corresponding configuration presents the same input symbol and work-tape symbols. Thus both machines consult the original transition from $q$ on those symbols. The transformed transition applies the original action while updating its stored output bit; compatibility of applying that action with the configuration map (`Complexity.acceptCfg_apply`) identifies the resulting configurations. This proves the step identity in both cases.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Complexity.acceptTM_loop`, `Turing.MultiTapeTM.step_of_halt`, `Complexity.acceptCfg_apply`.
