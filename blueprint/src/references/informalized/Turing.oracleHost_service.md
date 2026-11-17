<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_service -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Service Phase Simulation

**Claim.** From the service-phase encoding of the specified dispatch configuration with an empty argument word, the host reaches after exactly $2|z|+4+t$ steps the dispatch-phase encoding with argument word $[v]$.

**Proof.** The service procedure uses the source tape as a window containing the query word $z$, with the call machine’s tapes initially blank. The selected-tape and selected-head identities for embedded configurations show that this window has the required contents and head position (`Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`). The query-window lemma identifies each relevant cell with the corresponding cell of the call machine’s input word (`Turing.oracleQueryWindow`). The service-run simulation then shows that copying the word and executing the answer machine for $t$ steps leaves the verdict on the call tape and returns the copy routine to its exit state (`Turing.oracleService_run`). The untouched call bank is initially blank by the dispatch-configuration blankness lemma (`Turing.oracleDispatchCfg_callBlank`), and the source slot and call destination are distinct by injectivity of the slot map (`Turing.oracleSlots_injective`); thus the copy and call operations use the intended separate tapes. Updating the argument tape in the embedded dispatch configuration is equivalent to replacing the empty argument word by $[v]$ (`Turing.oracleEmbed_updateTape`, `Turing.oracleReadyCfg_replace`). The phase-host simulation carries the service run through its exit redirect into dispatch phase, adding the redirect transition (`Turing.phaseHostTM_run`). Combining its $2|z|+3+t$ service-and-copy steps with that transition gives $2|z|+4+t$.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.oracleQueryWindow`, `Turing.oracleDispatchCfg_callBlank`, `Turing.oracleSlots_injective`, `Turing.oracleService_run`, `Turing.oracleEmbed_updateTape`, `Turing.oracleReadyCfg_replace`, `Turing.phaseHostTM_run`.
