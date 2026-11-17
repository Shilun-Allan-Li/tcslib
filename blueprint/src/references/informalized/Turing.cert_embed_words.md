<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_embed_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding Tape Words

**Claim.** The embedded configuration with local words and frame words equals the standard configuration on the larger tape set with target words.

**Proof.** Compare the configurations field by field. Their states and input-head positions agree directly, and both have empty output. For each larger tape index in the image of the injection, write it as the image of a local index: the selected-tape property reduces its contents to the local buffer, which equals the target buffer by hypothesis; the selected-position property gives the local head position, which is zero. For an index outside the image, the frame property gives its contents and head position. The contents are the buffer of the frame word, which is the target word there by hypothesis, and the head position is zero. Thus every field agrees.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.runFrom_zero`, `Turing.embedEmitTM_frame`, `Turing.embedEmitCfg_selected_pos`.
