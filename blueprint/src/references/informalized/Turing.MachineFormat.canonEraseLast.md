<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonEraseLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Final Tape Cell

**Claim.** Erasing the cell at index $|w|$ from the tape that stores $w$ followed by $b$ leaves exactly the tape that stores $w$.

**Proof.** The tape representation of an appended symbol is obtained by updating the tape for $w$ at index $|w|$ with that symbol (`Turing.FinTM.bufferTape_append`). Updating this same location again with the empty value removes the appended cell. Since the tape for $w$ is already empty at index $|w|$, this second update does not change it, proving the result.

**Key facts.** `Turing.FinTM.bufferTape_append`.
