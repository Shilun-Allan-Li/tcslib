<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_runWith_setup_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting during the setup phase

**Claim.** If $P$ has halted by time $T_P$ without visiting $p_{\mathrm{exit}}$ earlier, then every choice word of length at least $T_P$ leaves the guess-and-run machine at the configuration reached by $P$ at time $T_P$, with its state placed in the pre-phase.

**Proof.** Consider the prefix of $w$ of length $T_P$. During this prefix the combined machine follows $P$ with its state embedded in the pre-phase. The simulation fact `NDTM.runWith_mapState_of_agreeOn_det` applies because, at every state visited before the end of the prefix, the first-visit hypothesis rules out $p_{\mathrm{exit}}$; hence the phase controller does not dispatch to the writer and each transition agrees with that of $P$. The prefix run is therefore the time-$T_P$ configuration of $P$, with its state embedded in the pre-phase. Split $w$ into this prefix and its remaining suffix using `NDTM.runWith_append`. Since $P$ is halted at time $T_P$, the embedded configuration is halted too, so the suffix leaves it unchanged by `NDTM.runWith_of_halt`. This proves the stated equality.

**Key facts.** `Turing.NDTM.runWith_mapState_of_agreeOn_det`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
