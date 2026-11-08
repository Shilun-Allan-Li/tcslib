<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_exists_scratchTemplateTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Scratch Template Construction

**Claim.** There are fixed finite control states and a fixed number of work tapes such that the embedded machine writes the joined record template into the designated blank tape, reaches its exit state within the stated linear time bound, avoids that state earlier, and keeps every work head within the stated radius.

**Proof.** Choose the scratch-template machine, its states, and its time constant from the existence theorem for writing record templates (`exists_recordTemplateTM`). Given the embedding and initial configuration, extract the embedded configuration on the selected tapes. The selected-configuration identity (`embedEmitCfg_select`) says that embedding this extracted configuration recovers the original one, including its other tapes and output. Apply the template-writing guarantee to the extracted configuration, using the supplied digit-value and tape-content hypotheses. The embedded machine follows this run exactly: the run-transport identity (`embedEmitTM_runFrom`) identifies each embedded time with the embedding of the corresponding extracted run. Consequently the first-exit property transfers directly. The head-radius bound transfers by the embedded-radius estimate (`rt_embed_radius`), and the final configuration has the claimed form by the embedding equality theorem (`embedEmitCfg_eq`): the selected scratch tape receives the template, while the unselected tapes retain their original contents.

**Key facts.** `Turing.exists_recordTemplateTM`, `Turing.embedEmitCfg_select`, `Turing.embedEmitTM_runFrom`, `Turing.rt_embed_radius`, `Turing.embedEmitCfg_eq`.
