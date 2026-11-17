<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.initCfg_eq_copyCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Copying Configuration

**Claim.** For every Boolean input, the copying machine's initial configuration is the copy configuration for an empty copied prefix with its copying head at position zero.

**Proof.** Compare the configuration fields. Both have the copy state, input-head position one (the copying head's position-zero convention), and empty output. In the initial machine configuration every work tape is blank and every work-tape head is at zero. In the copy configuration with copied-prefix length zero, the tape indexed by zero stores the empty prefix and all other tapes are blank, so all tapes are blank; its heads are likewise at zero. Thus each field agrees, and the configurations are equal.
