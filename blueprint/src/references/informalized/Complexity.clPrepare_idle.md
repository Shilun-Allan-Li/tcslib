<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrepare_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationarity at the Loader Return

**Claim.** Any preparation-machine configuration in the loader’s final-counter return state is unchanged by one step.

**Proof.** In the loader return state, the counter has reached its last value, so the loader’s transition takes the control-action branch. This action leaves every work tape and work-tape head unchanged, emits nothing, and keeps the state fixed. Its input-head movement is zero, which fixes the input position (`Turing.moveInputPos_zero`). Thus every component of the configuration is unchanged.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
