<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep Writes a Tape Zone

**Claim.** In $nk$ backward-sweep steps, the simulator processes the $n$ consecutive tape blocks in reverse order, writes the transition-updated blocks onto the left stack, and reaches frontier $z-nk$, while keeping the right stack, state data, input position, and output as stated.

**Proof.** Apply the reverse-sweep theorem (`sweep_run_reverse`) to the list of $n$ tape blocks in reverse order. Its transition hypothesis is exactly the backward writing behavior encoded by `writeVisit`: at each visited cell, the machine updates that tape’s symbol when the head flag is present, updates the head flags according to the prescribed movement, and moves one position left. The sweep theorem therefore says that the run consumes the supplied block list, folds these visits into the updated head flags, and prepends the resulting blocks to the left stack; the right stack and the other configuration data are preserved. The zone-update identity (`write_zone`) identifies this fold with the tape rows of the configuration obtained by applying the source action, with the head flags in their new positions. Finally, each row contains $k$ cells, so the zone length is $nk$ (`tapeZone_length`). Thus the run takes $nk$ steps and the frontier decreases by $nk$, giving the claimed endpoint.

**Key facts.** `Turing.FinTM.sweep_run_reverse`, `Turing.FinTM.write_zone`, `Turing.FinTM.tapeZone_length`.
