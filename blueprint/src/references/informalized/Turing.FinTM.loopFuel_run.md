<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopFuel_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relocation Preserves Fuel Runs

**Claim.** Running the relocated fuel source for any number of steps from the relocated fuel configuration agrees with relocating the fuel machine's configuration after the same number of steps.

**Proof.** View the relocated source as adding blank tapes to the left of the fuel machine's tapes. Its transition, on the original fuel-machine state, is exactly the fuel transition with those added tapes left untouched. The run-preservation fact for right-padded machines (`rightCfg_run`) therefore applies to the relocated initial configuration and yields the relocated fuel-machine run at time $t$.

**Key facts.** `Turing.FinTM.rightCfg_run`.
