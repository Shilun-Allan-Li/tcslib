<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.scan_write_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Scanned-Tape Writing Step

**Claim.** If the machine's transition on the configuration with the first $r$ symbols of $w$ written is to write $w[r]$, move tape $i$ right, and enter state $q'$, then one machine step produces the configuration with the first $r+1$ symbols written, input position moved by $m$, and the tape head advanced accordingly.

**Proof.** The assumed transition is exactly a write action on tape $i$, so the machine-step rule for such an action gives the new state, input-head movement, work-tape update at the scanned cell, and work-tape-head movement (`step_of_tapeAction_write`). It remains to identify the updated tape contents. On tape $i$, the scanned cell is the cell immediately after the already written prefix. Updating that cell with $w[r]$ extends the interval of cells described by the written prefix from length $r$ to length $r+1$, while leaving all other cells unchanged; this is the catalog-write extension identity (`catalog_write_take`). Every other tape is unchanged, and the head positions and remaining configuration fields agree by their definitions.

**Key facts.** `Turing.step_of_tapeAction_write`, `Turing.catalog_write_take`.
