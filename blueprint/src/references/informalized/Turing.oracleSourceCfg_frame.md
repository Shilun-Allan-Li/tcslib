<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleSourceCfg_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unused Oracle Source Tapes

**Claim.** Every host tape whose index is at least the end of the embedded source bank is blank everywhere and has its head at zero in the oracle source configuration.

**Proof.** The source bank embeds exactly the initial block of host tapes. If a host index were both in the range of this embedding and at least the stated bound, the explicit formula for the embedding would force its numerical index to be smaller than that bound. Thus the given index lies outside the source bank. The frame property of embedding and emission says that every tape outside the bank retains its supplied default tape and head position. Here those defaults are the blank tape and position zero, proving both assertions. (The frame property is `embedEmitTM_frame`.)

**Key facts.** `Turing.embedEmitTM_frame`.
