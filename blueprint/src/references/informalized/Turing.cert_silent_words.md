<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_silent_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent Embedding of Tape Words

**Claim.** Under the stated configuration hypotheses and with the capture tape empty, renaming the states of the silent embedding gives the standard configuration with tape assignment $w$.

**Proof.** Compare the fields of the two configurations. The state becomes the designated finish state by the assumed state of $d$, and the input-head position is already $1$. For a tape in the image of the injection, the selected-tape property reduces its contents to those of the corresponding local tape, which are the required buffer by hypothesis; the selected-position property gives head position zero. For a tape outside the image and different from the capture tape, the frame property preserves its buffer and zero head position. On the capture tape, the capture-field calculation gives the buffer of the empty prefix followed by $d$’s output, and its head position is the length of that word; since the output and assigned word are both empty, these are the empty buffer and position zero. Both configurations have empty output, so all fields agree.

**Key facts.** `Turing.embedSilentTM_frame`, `Turing.cert_capture_fields`, `Turing.embedSilentCfg_selected_tape`, `Turing.embedSilentCfg_selected_pos`.
