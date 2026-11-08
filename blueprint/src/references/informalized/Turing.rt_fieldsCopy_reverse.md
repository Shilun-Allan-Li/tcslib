<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_fieldsCopy_reverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Reverse Field Copying

**Claim.** For each fixed number of fields, a two-tape machine copies the joined fields from tape 1 to blank tape 0 within a linear time bound, avoids its exit state earlier, and keeps both heads within the stated radius.

**Proof.** Take the forward-copy machine provided by the existence theorem for copying a fixed number of fields (`exists_fieldsCopyTM`). Relabel its two work tapes by swapping their indices, so the source is now tape 1 and the destination tape 0. Form the corresponding swapped configuration. The selected-tape identities (`embedEmitCfg_selected_tape` and `embedEmitCfg_selected_pos`) show that its source record and blank destination satisfy the forward machine's hypotheses, with the same field list and joined length. Run the forward machine on this configuration. The run-transport identity (`embedEmitTM_runFrom`) says that the swapped machine's run is exactly the embedding of that run at every time. Hence its time bound, avoidance of the exit state, and head-radius bound transfer. At the final time, the forward machine's copied destination becomes tape 0 under the swap, while the source and all other cells are unchanged; the selected-tape identities and the swap's involution identify this with the claimed final configuration.

**Key facts.** `Turing.exists_fieldsCopyTM`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_runFrom`.
