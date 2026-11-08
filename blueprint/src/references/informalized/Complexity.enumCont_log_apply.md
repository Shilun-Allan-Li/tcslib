<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_log_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a logged step

**Claim.** Applying the logging action to the encoding of a configuration and its history yields the encoding of the updated configuration with one new history entry recording the symbols scanned before the step and the prescribed work-head movements.

**Proof.** Configurations are equal once their state, input-head position, work-tape contents, work-head positions, and output agree. The action preserves the encoded state, input-head movement, and output update exactly as it updates the source configuration. On the source work tapes, each tape either retains its contents or is updated at its current head position with the action's written symbol. The logging action performs precisely those same updates in the source-tape block. In the history blocks, the current scanned symbols and movement codes are written at the old history length, while the history length and corresponding head positions advance by one. The list-append identities for sparse history tapes (`Complexity.enumCont_sparse_append`) and for the buffer tape (`Turing.FinTM.bufferTape_append`) show that these point updates are exactly the encodings of the old histories with the new entry appended. Thus all configuration components agree with the encoding of the updated source configuration and extended history.

**Key facts.** `Complexity.enumCont_sparse_append`, `Turing.FinTM.bufferTape_append`.
