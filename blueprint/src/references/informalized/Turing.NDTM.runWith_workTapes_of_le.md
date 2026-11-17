<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.runWith_workTapes_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unvisited Work-Tape Cells Are Unchanged

**Claim.** If a cell position is at least the initial head position plus the length of the choice word, then its work-tape content is unchanged after the run.

**Proof.** Induct on the choice word, generalizing over the starting configuration. The empty word makes no change. For a word beginning with a bit, unfold the run into the first step and the remaining run (`Turing.NDTM.runWith_cons`). The head's displacement during a single step is at most one; this follows by applying the bound on head displacement during runs to a one-bit word (`Turing.NDTM.abs_runWith_workTapePos_sub_le`). Thus the assumed inequality for the full word implies the corresponding inequality for the remaining word from the post-step head position. The induction hypothesis says that the remaining run does not alter the cell. For the first step, a halted configuration is unchanged (`Turing.NDTM.stepWith_of_halt`). If the state is present, the step applies the transition action (`Turing.NDTM.stepWith_of_state`): that action either leaves the tape function unchanged or updates only the cell at the current head position. The displacement bound and the original inequality place the specified cell strictly beyond that position, so the update leaves its content unchanged as well.

**Key facts.** `Turing.NDTM.abs_runWith_workTapePos_sub_le`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.stepWith_of_halt`, `Turing.NDTM.stepWith_of_state`.
