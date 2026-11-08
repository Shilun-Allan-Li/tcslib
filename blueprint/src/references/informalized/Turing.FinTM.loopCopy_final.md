<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopCopy_final -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Copying Tape

**Claim.** When the entire word has been processed and the remaining suffix is empty, the copying tape is blank everywhere.

**Proof.** Fix an integer cell. If it lies before the processed prefix’s endpoint, the copying-tape definition makes it blank. Otherwise the cell is nonnegative, and the buffer of the empty word has no symbol there. In either case the tape value is blank, so it equals the blank buffer tape at every cell.
