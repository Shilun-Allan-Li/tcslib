<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.stepWith_mapState_of_agreeOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Renaming Preserves a Step

**Claim.** If the host machine's transitions on embedded good states are the state-renamed source transitions, then stepping the renamed configuration in the host machine agrees with renaming the result of a source-machine step.

**Proof.** Split according to the state of the source configuration. If it is empty, its renamed configuration also has empty state, and each step leaves its configuration unchanged (`stepWith_of_halt`), giving the desired equality. Otherwise write its state as $q$. The renamed configuration has state $e(q)$, and the assumption that every state present in the configuration is good lets us apply the transition-agreement hypothesis at $q$. The host transition is then exactly the state-renamed source transition, for the scanned input and work-tape symbols in the configuration. Applying that action to the renamed configuration gives the renamed result of applying the source action to the original configuration (`Cfg.mapState_apply`). This proves the equality in the nonempty-state case as well.

**Key facts.** `Turing.NDTM.stepWith_of_halt`, `Turing.Cfg.mapState_apply`.
