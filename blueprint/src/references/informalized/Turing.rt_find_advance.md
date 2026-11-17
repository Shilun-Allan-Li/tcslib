<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advance Through a Scanned Field

**Claim.** After the stated number of steps, the round machine has advanced past the scanned field and entered the phase-control state specified by the redirect, without visiting either distinguished read or exit state earlier.

**Proof.** The scan-phase result (`rt_find_scan_phase`) analyzes the forward scan and return across the word. It shows that after $2|w|+3$ steps the scan has completed with its accumulator folded over the word, the head in the position needed for skipping, and no earlier visit to either distinguished state. The assumed redirect identifies this completed scan with the skip phase carrying $b$. Regard the same configuration as the skip machine's starting configuration; the skip-phase result (`rt_find_skip_phase`) shows that in a further $|w|+2$ steps the head passes the separator and the specified redirect leads to $q$, again with neither distinguished state visited earlier. Concatenate these runs using the run-addition law (`MultiTapeTM.runFrom_add`). Since $(2|w|+3)+(|w|+2)=3|w|+5$, the head has advanced by $|w|+1$, the resulting state is $q$, and all earlier times are covered by one of the two phase bounds.

**Key facts.** `Turing.rt_find_scan_phase`, `Turing.rt_find_skip_phase`, `Turing.MultiTapeTM.runFrom_add`.
