<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_clear_snapshot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing a Snapshot Buffer

**Claim.** Starting from the sweep snapshot, clearing the designated tape takes exactly $2|w|+2$ steps, empties its buffer, and leaves the other buffer unchanged. The machine does not reach `done` earlier, and the heads satisfy the stated bounds throughout the run.

**Proof.** First, the hypothesis identifying the destination as tape 1 or tape 3, together with the corresponding buffer equality, shows that the contents seen along the destination tape from offset $-1$ through $|w|$ agree with the word $w$ stored for the clearing pass. Apply the clearing-run theorem (`Turing.clearTM_run_ofCfg`): the forward sweep crosses the $|w|$ symbols and detects the blank, then the return sweep erases those symbols and reaches `done` after $2|w|+2$ steps; it also gives the strict preterminal-state assertion and the head bounds. To identify its final tape contents with the claimed snapshot, compare tape cells relative to the destination origin. Inside the interval occupied by the buffer the clearing theorem has erased the cells. Outside that interval, the original buffer lookup is already blank: on the left this follows from the negative-index convention, and on the right from the fact that list lookup past the word's length is blank. Thus the destination buffer is empty everywhere. The other buffer and all remaining snapshot data are unchanged. The theorem's interval bound gives the destination head range, and its unchanged-head clause gives the assertion for every other tape; the snapshot's tape-0 offset cancels when measuring those heads against their original positions.

**Key facts.** `Turing.clearTM_run_ofCfg`.
