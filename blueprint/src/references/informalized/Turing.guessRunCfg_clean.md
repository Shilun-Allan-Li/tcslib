<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunCfg_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Embedded Configuration

**Claim.** Under the stated embedding and blankness hypotheses, the guessed-run construction on the specified configuration equals the embedded silent configuration of the stream-start configuration.

**Proof.** First instantiate the embedded-machine frame property with a one-state machine whose transition leaves every tape and head unchanged. At time zero, the frame property says that each tape outside the embedding and distinct from the capture tape retains its prescribed blank contents and zero head position; the zero-time run is the original configuration (`runFrom_zero`). It remains to compare configuration fields. The state and input-head position agree directly. For a tape in the image of the embedding, use the selected-tape property (`embedSilentCfg_selected_tape`). If its source index is $jR$, the guessed configuration writes the word $s$ starting at the head position. On the interval of offsets $0,dots,m-1$, this agrees with the stream-start buffer; outside that interval, the blankness hypothesis on $blk$ makes both contents blank. If the source index differs from $jR$, injectivity ensures the update at $jR$ does not affect that tape, so both sides are blank. For a tape outside the image, split into the capture tape and all other tapes. The capture-tape property (`embedSilentCfg_cap`) identifies its contents with the buffer for the empty capture word and its head position with the length of that word, namely zero. Every other such tape agrees by the frame property. Finally, for head positions on embedded tapes, the selected-position property (`embedSilentCfg_selected_pos`) reduces equality to the all-zero heads of the stream-start configuration. The capture head is zero by the same capture-tape property, and the remaining outside heads agree by the frame property. The output fields are both empty.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.embedSilentTM_frame`, `Turing.embedSilentCfg_selected_tape`, `Turing.embedSilentCfg_cap`, `Turing.embedSilentCfg_selected_pos`.
