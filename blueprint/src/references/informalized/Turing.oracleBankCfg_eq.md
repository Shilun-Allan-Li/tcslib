<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleBankCfg_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of embedded configurations

**Claim.** If a configuration and its embedding agree in state, input-head position, and output, and agree on the contents and head positions of every selected tape, then embedding it with the larger configuration's data on unselected tapes and with an empty output prefix yields that larger configuration.

**Proof.** Configurations are equal once their state, input-head position, work-tape contents, work-tape head positions, and output agree. The state and input-head components agree by hypothesis. The output of the embedding is the empty prefix followed by the smaller configuration's output, so it equals the larger output by hypothesis.

For each work-tape index in the larger machine, split into whether it lies in the embedding's range. If it is the image of an index $i$, the embedding selects the smaller configuration's tape and head position there (Turing.embedEmitCfg_selected_tape and Turing.embedEmitCfg_selected_pos); the hypotheses identify both with the corresponding data in the larger configuration. If it is outside the range, the embedding uses the larger configuration's own tape and head data, and these remain unchanged by the frame property at time zero (Turing.embedEmitTM_frame). Thus every component agrees, proving equality.

**Key facts.** `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitTM_frame`.
