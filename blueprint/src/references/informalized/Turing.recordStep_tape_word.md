<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_tape_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorded Tape Word After an Action

**Claim.** Writing the marked tape cell and then shifting its mark according to the action’s head movement yields exactly the recorded tape word of the resulting configuration.

**Proof.** First use the scan-map identity (`Turing.scanResult_map`) to express the writing pass as applying the write operation independently to every symbol of the old word. The cell-write identity (`Turing.recordStep_cell_write`) identifies each such symbol with the corresponding cell of the action-updated tape, while retaining the old head mark. The remaining mark-shift pass is exactly the finite-window shift identity (`Turing.recordStep_cell_shift`): under the head-in-window hypothesis, shifting the mark by the action’s movement places it at the new head position, with the tape contents unchanged. Combining these pointwise identifications gives the claimed word.

**Key facts.** `Turing.scanResult_map`, `Turing.recordStep_cell_write`, `Turing.recordStep_cell_shift`.
