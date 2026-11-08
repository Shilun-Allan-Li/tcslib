<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_embed_refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity Embedding of a Configuration

**Claim.** Embedding a configuration into the same set of tapes by the identity embedding, with empty output prefix, leaves the configuration unchanged.

**Proof.** Compare the configurations component by component. Their state, input-head position, and output agree directly, since the output prefix is empty. Every tape is selected by the identity embedding, so its contents and head position agree with those of the original configuration; these are exactly the selected-tape and selected-head properties (`Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`). Thus all components agree.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`.
