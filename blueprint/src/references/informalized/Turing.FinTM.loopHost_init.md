<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Loop Host Configuration

**Claim.** The loop host's initial configuration on input $x$ is the capture configuration of the relocated fuel machine's initial configuration, with its fuel state embedded in the host control states and empty capture buffers.

**Proof.** Rewrite each machine's initial configuration as the configuration formed from its initial state and entirely blank work tapes, using `initCfg_ofWords`. The fuel source relocates the fuel machine's work tapes without changing its initial state or input head. Capturing this initial configuration with empty prefixes and output buffers gives the same embedded initial state, input position, blank tapes, zero head positions, and empty output as the loop host's initial configuration. Hence the configurations agree componentwise.

**Key facts.** `Turing.initCfg_ofWords`.
