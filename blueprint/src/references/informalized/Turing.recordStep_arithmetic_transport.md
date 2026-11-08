<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_arithmetic_transport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Binary Arithmetic Transport

**Claim.** The embedded arithmetic machine updates the selected encoded digit bank from $w$ to $v$ within the stated time, avoids its done states beforehand, and keeps all heads within the stated displacement bound.

**Proof.** Decode the selected bank of the four-tape configuration to a one-tape Boolean configuration. The buffer-encoding identities (`FinTM.bufferTape_map`, `FinTM.bufferTape_map_decode`) show that the selected bank represents exactly $w$, with the same head position; all other tapes are unaffected by the embedding. If `increase` is true, the increment run theorem applies using the assumed fixed-width result; otherwise the decrement run theorem applies. In either case, it supplies a run reaching the done-true state with the bank containing $v$, together with avoidance of done states at earlier times and a bound on the selected head's displacement. The prefix length used by that arithmetic run is at most $|w|$, so its time is at most $2|w|+2$ and its head displacement at most $|w|+1$. The transport identity (`recordStep_transport`) carries the Boolean run to the encoded, embedded machine run. The selected-tape and selected-position identities (`embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`) identify the updated bank, while the frame property (`embedEmitTM_frame`) keeps all other tapes and heads unchanged. The final tape equality uses equal lengths of $v$ and $w$ to extend the agreement on the represented word to every cell.

**Key facts.** `Turing.FinTM.bufferTape_map_decode`, `Turing.decrementTM_run_succ_ofCfg`, `Turing.incrementTM_run_succ_ofCfg`, `Turing.recordStep_transport`, `Turing.embedEmitTM_frame`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.MultiTapeTM.runFrom_zero`.
