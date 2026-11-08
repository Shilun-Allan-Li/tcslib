<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_shadow_pre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded counter tape agreement

**Claim.** Decoding the configuration preserves its run state, and at every specified offset the decoded work tape contains exactly the corresponding Boolean buffer-tape symbol.

**Proof.** Let $D$ be the configuration with state $\mathrm{run}$, tape $c_t$, and head position $c_p$. Decoding preserves the state and work-head positions (`Cfg.decodeSymbols_state`, `Cfg.decodeSymbols_workTapePos`), and the decoded work-tape content at a position is obtained by binding the original content through the Boolean decoder (`Cfg.decodeSymbols_workTapes`). At the position $c_p+p$, the tape hypothesis identifies the original content with the encoded buffer-tape content of $w$. Decoding that content gives the Boolean buffer-tape content of $w$ (`FinTM.bufferTape_map_decode`), proving the asserted equality for every allowed offset.

**Key facts.** `Turing.Cfg.decodeSymbols_state`, `Turing.Cfg.decodeSymbols_workTapePos`, `Turing.Cfg.decodeSymbols_workTapes`, `Turing.FinTM.bufferTape_map_decode`.
