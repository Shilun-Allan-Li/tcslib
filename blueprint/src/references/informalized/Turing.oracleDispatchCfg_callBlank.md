<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleDispatchCfg_callBlank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Call Tapes After Dispatch Embedding

**Claim.** If the dispatch configuration's fourth work tape is blank everywhere and its head is at zero, then each of the call-bank tapes in its embedded host configuration is blank everywhere and has head at zero.

**Proof.** First handle the distinguished call-bank index corresponding to the dispatch machine's fourth tape. The embedding preserves the contents and head position of every selected tape (`embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`), so the hypotheses give blank contents and head position zero there. For any other call-bank index, it is not among the dispatch machine's selected tape slots. The embedding frame property says such an unselected host tape retains its background contents and head position (`embedEmitTM_frame`). The source configuration's frame property says those background call-bank tapes are blank and have head zero (`oracleSourceCfg_frame`). Combining these facts proves the claim for every call-bank index. The injectivity of the selected-slot map ensures the embedding is well-defined (`oracleSlots_injective`).

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`, `Turing.oracleSourceCfg_frame`, `Turing.oracleSlots_injective`.
