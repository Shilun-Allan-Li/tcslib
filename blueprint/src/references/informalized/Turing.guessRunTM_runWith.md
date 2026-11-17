<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run-and-Verdict Simulation

**Claim.** If the guessed segment of a sufficiently long choice word is $s$, and $Q$ first reaches an accepting or rejecting verdict at time $T_Q$, then the guess-and-run machine halts with the simulated configuration's tape data and appends the bit indicating acceptance to its output.

**Proof.** First use the handoff result (`guessRunTM_runWith_handoff`) on the initial $T_P+2m+9$ choice bits. The first $T_P+1$ bits bring $P$ to its first exit state; the next $m$ bits write the guessed word $s$. The blank cells flanking the original block let the skip and rewind phases locate the block's end and return its head to the start. The resulting configuration is the entry configuration for $Q$, with the other tape data preserved. The guessed segment extracted from this prefix is still $s$, by the given condition on the full word. Split the remaining choices so that the first $T_Q$ bits run the $Q$ phase to its stated configuration $d$; the deterministic-machine simulation fact (`MultiTapeTM.toNDTM_runWith`) identifies this phase with the ordinary run of $Q$. Since $d$ is an accepting or rejecting verdict and neither verdict occurred earlier, the phase-host simulation theorem (`NDTM.phaseHostND_run`) carries the run through time $T_Q$ without an earlier phase change. At the verdict, the phase controller dispatches once into the output phase. Its transition leaves the input position, work tapes, and work-head positions unchanged, appends the Boolean indicating whether $d$ is accepting, and halts. The length bound guarantees a choice bit for this dispatch; any remaining bits leave the halted configuration unchanged (`NDTM.runWith_of_halt`). Decomposing the full choice word into its initial segment and remainder uses the concatenation law for runs (`NDTM.runWith_append`), with the one-bit dispatch expressed by the cons law (`NDTM.runWith_cons`).

**Key facts.** `Turing.guessRunTM_runWith_handoff`, `Turing.MultiTapeTM.toNDTM_runWith`, `Turing.NDTM.phaseHostND_run`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_of_halt`.
