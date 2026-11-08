# Existing public readers and homes

All bind to source `f631647190998272127fcd37b7a5d1e61fac4f3f`. These are existing names used by the final six bodies/two header proposals. The current screen agent confirmed every home is already in the exact previous MIG25 population.

`TCSlib/Complexity/TuringMachine/Finite.lean`

`Turing.MultiTapeTM.exists_first_halt`, `Turing.MultiTapeTM.exists_first_entry_of_fixed`, `Turing.FinTM.computesInTime_iff`.

`TCSlib/Complexity/TuringMachine/Deterministic.lean`

`Turing.MultiTapeTM.initCfg_eq`, `Turing.MultiTapeTM.step_of_halt`, `Turing.MultiTapeTM.step_of_some`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.timed_input_bound`.

`TCSlib/Complexity/TuringMachine/Configuration.lean`

`Turing.Cfg.ext`, `Turing.moveInputPos_zero`, `Turing.inputSymbolInner`, `Turing.Cfg.init_state`, `Turing.Cfg.init_inputPos`, `Turing.Cfg.init_workTapes`, `Turing.Cfg.init_workTapePos`, `Turing.Cfg.init_output`, `Turing.Cfg.workTapeSymbols_eq`, `Turing.Cfg.inputSymbol_of_zero`, `Turing.Cfg.inputSymbol_of_end`, `Turing.Action.apply_state`, `Turing.Action.apply_inputPos`, `Turing.Action.apply_workTapePos`, `Turing.Action.apply_output`.

`TCSlib/Complexity/TuringMachine/StateRenaming.lean`

`Turing.Cfg.mapState_state`, `Turing.Cfg.mapState_inputPos`, `Turing.Cfg.mapState_workTapes`, `Turing.Cfg.mapState_workTapePos`, `Turing.Cfg.mapState_apply`.

`TCSlib/Complexity/TuringMachine/Simulation.lean`

`Turing.Action.apply_workTapes`, `Turing.FinTM.VirtualTag_iff`, `Turing.FinTM.bufferedSecondCfg_state`, `Turing.FinTM.bufferTape_nil`, `Turing.FinTM.branchTM_k`, `Turing.FinTM.branchTM_State`, `Turing.FinTM.rewind_from_any`, `Turing.FinTM.timed_rewind`, `Turing.FinTM.leftCfg_state`, `Turing.FinTM.leftCfg_inputPos`, `Turing.FinTM.rightCfg_state`, `Turing.FinTM.rightCfg_inputPos`, `Turing.FinTM.rightCfg_workTapes`, `Turing.FinTM.rightCfg_workTapePos`, `Turing.FinTM.rightCfg_output`.

`TCSlib/Complexity/TuringMachine/Build/Wrappers.lean`

`Turing.capture_run`, `Turing.captureCfg_state`, `Turing.captureCfg_inputPos`, `Turing.captureCfg_workTapes`, `Turing.captureCfg_workTapePos`, `Turing.captureCfg_output`.

`Turing.Cfg.inputSymbol_congr` is not used or imported. The two first-event API declarations are owned by `Finite.lean`; an earlier direct message incorrectly grouped them under `Deterministic.lean`, and that message was corrected.
