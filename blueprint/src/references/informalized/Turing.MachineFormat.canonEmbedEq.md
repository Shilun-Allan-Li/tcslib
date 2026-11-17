<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonEmbedEq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Configuration Equality

**Claim.** Under the stated agreement of states, input positions, outputs, selected tape contents and heads, and the supplied contents and heads outside the embedding, embedding the smaller configuration with empty output prefix gives exactly the larger configuration.

**Proof.** Configurations are equal once their state, input position, tape contents, tape-head positions, and output agree. The first two components agree by hypothesis. The output of the embedding with empty prefix is the smaller configuration’s output, so it agrees by the output hypothesis. For each embedded index, the embedding’s tape contents and head position are those of the corresponding smaller tape (`Turing.embedEmitCfg_selected_tape` and `Turing.embedEmitCfg_selected_pos`); the selected-tape hypotheses identify these with the larger configuration. For an index outside the image, the embedding run frame property at time zero says that its tape and head position remain the supplied ones (`Turing.embedEmitTM_frame`); the outside hypotheses identify those with the larger configuration. Thus every component agrees, proving equality.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
