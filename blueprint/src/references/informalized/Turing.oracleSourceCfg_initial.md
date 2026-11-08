<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleSourceCfg_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Oracle Source Configuration

**Claim.** Embedding the initial oracle configuration with the true side agrees with the specified host configuration, except that the embedded query tape is replaced by the tape containing true at zero and blank elsewhere.

**Proof.** Compare the tape contents and head positions separately. Every host tape in the source bank is selected from the embedded configuration, so its contents and head position are inherited from the corresponding tape of the shadow configuration. The selected-tape and selected-position properties of embedding justify these identifications (`embedEmitCfg_selected_tape` and `embedEmitCfg_selected_pos`). Split the source-bank index into the ordinary tapes and its final, query-tape index. On the ordinary tapes, the shadow configuration preserves the original initial tape contents and zero head positions, which agree with the corresponding prefix words of the host configuration. At the query index, the shadow configuration supplies the oracle-origin tape instead; this is precisely the stated replacement. For indices outside the source bank, the frame property gives a blank tape and head at zero (`oracleSourceCfg_frame`). Such an index is beyond the original input-word prefix, so the host configuration also has the blank default there, and it cannot be the query index. The two configurations therefore agree on every tape and head; their states, input positions, and outputs agree directly from their definitions. Extensionality of configurations gives the claimed equality.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.oracleSourceCfg_frame`.
