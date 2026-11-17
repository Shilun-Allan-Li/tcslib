<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.Cfg.init_eq_ofWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration from Empty Tape Words

**Claim.** For any number $k$ of work tapes, state $q$, and Boolean input word $x$, the initial configuration on $x$ with state $q$ equals the configuration formed from $q$ and the family of empty words on all work tapes.

**Proof.** Regard $q$ and the empty work-tape words as the initial state and empty tapes of a multitape machine. The fact that initializing any such machine yields the configuration formed from its start state and empty work-tape words (`Turing.initCfg_ofWords`) identifies that machine's initial configuration with the stated configuration. For this machine, the initial configuration is precisely the given initial configuration on $x$ with state $q$, so the claimed equality follows.

**Key facts.** `Turing.initCfg_ofWords`.
