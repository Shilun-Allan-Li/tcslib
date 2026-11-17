<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordSkipTM_path -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path of the Recording and Skip Machine

**Claim.** Throughout the specified run, the input position, tape contents, and output remain unchanged; the table-tape head advances first through the fixed-width record and then through the successor-state field, while other heads stay put. Before the full run ends, the machine is not in a tagged done state.

**Proof.** Split on whether $u\le 4k+4$. In this initial segment, the fixed-width recording result identifies the run with the read configuration at position $u$ (`Turing.StepBlock.recordSkipTM_fixed`). Its definition changes only the state and the table-tape head, yielding the asserted unchanged input position, tape contents, and output, and the stated head displacement. This configuration is not a tagged done state. For the remaining steps, regard the full-width read configuration, now in the tag phase, as the starting point. The assumed bits following the record are exactly the serialization of $s$, so the source tape contains the required state-field word. The run splits into the fixed prefix and the remaining suffix by the iteration law for runs (`Turing.MultiTapeTM.runFrom_add`); `Turing.StepBlock.recordSkipTM_tail` identifies that suffix with the successor-field machine. Its head-position theorem gives the claimed displacement, and its trace theorem describes the state during the scan. Finally, its cut theorem ensures that before the entire state-field word has been consumed, the state cannot be done. Since state renaming preserves inequality, the same exclusion holds for the tagged machine state.

**Key facts.** `Turing.StepBlock.recordSkipTM_fixed`, `Turing.MultiTapeTM.runFrom_add`, `Turing.StepBlock.recordSkipTM_tail`, `Turing.StepBlock.succFieldTM_heads`, `Turing.StepBlock.succFieldTM_trace`, `Turing.StepBlock.succFieldTM_cut`, `Turing.StepBlock.summary_ne_table`.
