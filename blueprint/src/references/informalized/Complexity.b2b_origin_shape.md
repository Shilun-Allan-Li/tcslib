<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_origin_shape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape of an Embedded Configuration

**Claim.** Embedding the virtual-input configuration into the $k$ work tapes produces the stated state, input-head position, tape contents, work-head positions, and output.

**Proof.** The state, input-head position, and output follow directly from the definitions of the virtual-host configuration and its embedding. For the tape indexed by $U$, the single simulated tape is placed at that index, and its contents are the buffer storing $y$; the selected-tape identity (`Turing.embedEmitCfg_selected_tape`) and selected-head identity (`Turing.embedEmitCfg_selected_pos`) give these two coordinates. Every index other than $U$ lies outside the range of the single-tape embedding, so the embedding frame property (`Turing.embedEmitTM_frame`), applied at time zero, says those tapes and their heads retain the initially blank contents and zero positions. These coordinate identities are exactly the asserted configuration equality.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
