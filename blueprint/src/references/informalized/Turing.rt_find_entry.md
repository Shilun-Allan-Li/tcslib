<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entry into a Search Round

**Claim.** Starting in the initial read control with tape 0 encoding a list of nonempty fields, the round machine reaches either the next read control or the exit control within the stated linear time bound. The first positive time it reaches either control is the exhibited time; before then it is in neither. The final head displacement is the offset through the first $m-1$ fields if the folded state is accepted, and the offset after all $m$ fields otherwise.

**Proof.** First, the nonemptiness of the first field ensures that the cell under tape 0's head contains a symbol. The tape-encoding identity `fieldsTape_field` identifies this cell with the first symbol of that field, so the machine's initial read phase records `true`. The two-step read behavior (`rt_find_read`) therefore sends the machine into the forward scan of field $0$. Apply the induction theorem for running through the remaining fields (`rt_find_fields_run`) from this scan state. It supplies a bounded scan time, excludes the read and exit controls at all earlier scan times, and gives the resulting head displacement and terminal control according to whether the fold is accepted. Combining the initial two steps with that run gives the claimed terminal configuration; the time bound follows from the scan bound and the joined tape length. For an intermediate time $u$, the first step is the read phase with a stored bit, hence is neither distinguished control. At later times before the terminal time, split off the first two steps and use the scan theorem's exclusion. The run has non-`none` state throughout this interval because its terminal state is non-`none`, by persistence of a nonhalting state (`runFrom_state_ne_none_of_le`). Thus each intermediate state has a phase and control, and the exclusions give the assertion.

**Key facts.** `Turing.fieldsTape_field`, `Turing.rt_find_read`, `Turing.rt_find_fields_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`.
