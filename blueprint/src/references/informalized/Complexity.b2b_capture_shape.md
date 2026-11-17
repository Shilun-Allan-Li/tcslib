<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_capture_shape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape of a Captured Configuration

**Claim.** Embedding an initial configuration with output $y$ into the larger machine places the buffered word $y$ and a head at its length on the capture tape, while the embedded tapes remain blank and their heads remain at zero.

**Proof.** Compare tape contents and head positions. At the capture index, which lies outside the embedding image, the embedded-configuration capture identity (`Turing.embedSilentCfg_cap`) gives the buffer for the empty prefix followed by $y$, namely the buffer for $y$, and places the head at $|y|$. On an embedded tape, the selected-tape identity (`Turing.embedSilentCfg_selected_tape`) gives the original tape contents, which are blank by the hypothesis; the selected-head identity (`Turing.embedSilentCfg_selected_pos`) gives its original head position, zero in the initial configuration. On every other index, the zero-time framing property (`Turing.embedSilentTM_frame`) preserves the specified tape contents and head positions. The state and input position are unchanged by embedding, and the initial configuration's output field is empty, as on the right-hand side. These componentwise agreements establish the configuration equality.

**Key facts.** `Turing.embedSilentCfg_cap`, `Turing.embedSilentCfg_selected_tape`, `Turing.embedSilentCfg_selected_pos`, `Turing.embedSilentTM_frame`.
