<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_embed_cfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding the initial buffer configuration

**Claim.** If the tape-index injection sends tape $0$ to tape $0$, embedding the initial configuration with $w$ on its first tape, blank contents on unused tapes, heads at the origin, and empty output gives the corresponding initial configuration on $k$ tapes.

**Proof.** Compare the configuration components. State, input-head position, and output agree directly. For tape contents, first consider an index in the image of the injection. The selected-tape property of the embedding identifies its contents with the corresponding source tape. Injectivity and the assumption that tape $0$ maps to tape $0$ ensure that this is the distinguished first tape exactly when the source index is $0; otherwise both configurations have blank contents there. For an index outside the image, the embedding frame property says its tape remains blank. The same split handles head positions: selected indices inherit their source head positions, all of which start at zero, and unselected indices retain the prescribed zero head. Hence all components agree.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitTM_frame`, `Turing.embedEmitCfg_selected_pos`.
