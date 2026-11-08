<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.stepWith_hostCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Host step from a host configuration

**Claim.** From any host configuration built from the specified tapes, positions, input, and phase, one host step equals applying the host transition action to that phase, choice, scanned input symbol, and scanned work-tape symbols.

**Proof.** The host configuration has its state equal to the specified phase, so the machine's step rule for a present state applies: one step is the action given by its transition function at the choice bit and the symbols currently scanned. This is exactly the stated right-hand side.

**Key facts.** `Turing.NDTM.stepWith_of_state`.
