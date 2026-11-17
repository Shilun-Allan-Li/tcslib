<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleSource_localView -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local View of the Oracle Source Configuration

**Claim.** Embedding the four-tape local configuration into the oracle source configuration yields that configuration with its state replaced by the chosen dispatch state.

**Proof.** Match the four local tapes with their designated host tapes. The first is the query tape, with its contents and head position inherited from the source configuration; the selected-tape and selected-position properties of embedding establish these matches (`embedEmitCfg_selected_tape` and `embedEmitCfg_selected_pos`). The second is the oracle-origin tape, again with its contents and head supplied by the shadow configuration. The third and fourth designated host tapes lie outside the source bank, so the frame property identifies them as blank with heads at zero (`oracleSourceCfg_frame`); these are exactly the local configuration's remaining tapes. The four designated slots are distinct (`oracleSlots_injective`), as required to apply the bank comparison. Now compare state, input position, and output: since the source state is present, replacing its mapped state by the constant dispatch state gives the local configuration's state; input positions are the same, and the local output is the source output. The bank-equality principle says that when these fields agree and the local tapes and heads match the designated host slots, embedding the local configuration into the host configuration recovers the host configuration (`oracleBankCfg_eq`). Applying it gives the claimed equality.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.oracleSourceCfg_frame`, `Turing.oracleSlots_injective`, `Turing.oracleBankCfg_eq`.
