| line | tactic | argument | classification |
|---|---|---|---|
| 84 | `rw` | `MultiTapeTM.initCfg_eq` | theorem (other file) |
| 86 | `simp only` | `Cfg.init_state` | theorem (other file) |
| 87 | `simp only` | `Cfg.init_inputPos` | theorem (other file) |
| 88 | `simp only` | `Cfg.init_output` | theorem (other file) |
| 88 | `simp only` | `List.append_nil` | core or Mathlib lemma |
| 92 | `simp only` | `Cfg.init_workTapes` | theorem (other file) |
| 93 | `simp only` | `Cfg.init_workTapePos` | theorem (other file) |
| 98 | `rw` | `hq` | local hypothesis |
| 98 | `rw` | `hinit` | local hypothesis |
| 98 | `rw` | `hr` | local hypothesis |
| 98 | `rw` | `embedEmitTM_runFrom` | theorem (other file) |
| 107 | `rw` | `computesInTime_iff` | theorem (other file) |
| 108 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 110 | `rw` | `hrun` | local hypothesis |
| 110 | `rw` | `embedEmitCfg_state` | theorem (other file) |
| 110 | `rw` | `hs` | local hypothesis |
| 111 | `rw` | `hrun` | local hypothesis |
| 111 | `rw` | `embedEmitCfg_output` | theorem (other file) |
| 111 | `rw` | `ho` | local hypothesis |
| 111 | `rw` | `List.nil_append` | core or Mathlib lemma |
| 116 | `rw` | `hrun` | local hypothesis |
| 116 | `rw` | `embedEmitCfg_state` | theorem (other file) |
| 117 | `rw` | `hrun` | local hypothesis |
| 117 | `rw` | `embedEmitCfg_output` | theorem (other file) |
| 117 | `rw` | `List.nil_append` | core or Mathlib lemma |
| 151 | `rw` | `hinl` | local hypothesis |
| 153 | `rw` | `Nat.mul_assoc` | core or Mathlib lemma |
| 251 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 291 | `rw` | `MultiTapeTM.step_of_some` | theorem (other file) |
| 293 | `rw` | `Action.apply_state` | theorem (other file) |
| 293 | `rw` | `hW` | local hypothesis |
| 295 | `rw` | `Action.apply_inputPos` | theorem (other file) |
| 295 | `rw` | `hW` | local hypothesis |
| 298 | `rw` | `Action.apply_workTapes` | theorem (other file) |
| 298 | `rw` | `Cfg.workTapeSymbols_eq` | theorem (other file) |
| 298 | `rw` | `hW` | local hypothesis |
| 302 | `rw` | `tt_leafTM_tr_workTapes_of_ne` | own definition/lemma |
| 302 | `rw` | `Option.getD_none` | core or Mathlib lemma |
| 302 | `rw` | `Function.update_eq_self` | core or Mathlib lemma |
| 303 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 304 | `rw` | `if_neg` | core or Mathlib lemma |
| 306 | `rw` | `Action.apply_workTapePos` | theorem (other file) |
| 306 | `rw` | `tt_leafTM_tr_moves` | own definition/lemma |
| 306 | `rw` | `SignType.coe_zero` | core or Mathlib lemma |
| 306 | `rw` | `add_zero` | core or Mathlib lemma |
| 307 | `rw` | `Action.apply_output` | theorem (other file) |
| 307 | `rw` | `hW` | local hypothesis |
| 464 | `rw` | `hs₀` | local hypothesis |
| 469 | `rw` | `h0` | local hypothesis |
| 472 | `rw` | `hb` | local hypothesis |
| 477 | `rw` | `hp0` | local hypothesis |
| 480 | `rw` | `h1` | local hypothesis |
| 529 | `rw` | `hb` | local hypothesis |
| 540 | `rw` | `hT` | local hypothesis |
| 540 | `rw` | `hD` | local hypothesis |
| 542 | `rw` | `H.2` | local hypothesis |
| 542 | `rw` | `hc` | local hypothesis |
| 542 | `rw` | `tt_cfg_mapState` | own definition/lemma |
| 550 | `rw` | `hR` | local hypothesis |
| 550 | `rw` | `F.pre` | local hypothesis |
| 557 | `rw` | `h` | local hypothesis |
| 575 | `rw` | `hT` | local hypothesis |
| 575 | `rw` | `hD` | local hypothesis |
| 575 | `rw` | `hI` | local hypothesis |
| 577 | `rw` | `H.2` | local hypothesis |
| 578 | `rw` | `hs'` | local hypothesis |
| 579 | `rw` | `H.1` | local hypothesis |
| 579 | `rw` | `Set.mem_singleton_iff` | core or Mathlib lemma |
| 579 | `rw` | `Cfg.mapState_state` | theorem (other file) |
| 584 | `rw` | `R.run` | local hypothesis |
| 584 | `rw` | `hs'` | local hypothesis |
| 655 | `rw` | `hend` | local hypothesis |
| 662 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 664 | `rw` | `hs` | local hypothesis |
| 664 | `rw` | `hD` | local hypothesis |
| 664 | `rw` | `hτ` | local hypothesis |
| 664 | `rw` | `hn` | local hypothesis |
| 708 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 712 | `rw` | `hr` | local hypothesis |
| 712 | `rw` | `hR` | local hypothesis |
| 712 | `rw` | `hinp` | local hypothesis |
| 713 | `change` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 728 | `rw` | `Nat.lt_one_iff.mp` | core or Mathlib lemma |
| 728 | `rw` | `h₀` | local hypothesis |
| 734 | `rw` | `H` | local hypothesis |
| 734 | `rw` | `h1` | local hypothesis |
| 734 | `rw` | `hstep` | local hypothesis |
| 736 | `rw` | `Cfg.mapState_state` | theorem (other file) |
| 737 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 738 | `rw` | `hn` | local hypothesis |
| 740 | `rw` | `Cfg.mapState_output` | theorem (other file) |
| 743 | `rw` | `hstep` | local hypothesis |
| 744 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 745 | `rw` | `hq'` | local hypothesis |
| 749 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 750 | `rw` | `show` | core or Mathlib lemma |
| 757 | `rw` | `hs₁` | local hypothesis |
| 759 | `rw` | `hstep` | local hypothesis |
| 761 | `rw` | `hstep` | local hypothesis |
| 765 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 766 | `rw` | `Function.update_idem` | core or Mathlib lemma |
| 766 | `rw` | `zonedTape_homeWrite` | theorem (other file) |
| 768 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 769 | `rw` | `if_neg` | core or Mathlib lemma |
| 769 | `rw` | `if_neg` | core or Mathlib lemma |
| 770 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 771 | `rw` | `if_neg` | core or Mathlib lemma |
| 772 | `rw` | `hstep` | local hypothesis |
| 774 | `rw` | `hstep` | local hypothesis |
| 782 | `rw` | `H.1` | local hypothesis |
| 782 | `rw` | `Set.mem_singleton_iff` | core or Mathlib lemma |
| 782 | `rw` | `Cfg.mapState_state` | theorem (other file) |
| 784 | `rw` | `Nat.lt_one_iff.mp` | core or Mathlib lemma |
| 784 | `rw` | `h₀` | local hypothesis |
| 787 | `rw` | `h1` | local hypothesis |
| 787 | `rw` | `hs₁` | local hypothesis |
| 798 | `rw` | `tt_τ_of_lt` | own definition/lemma |
| 798 | `rw` | `Nat.add_le_add_iff_right` | core or Mathlib lemma |
| 819 | `rw` | `zoneHomeWrite_left` | theorem (other file) |
| 819 | `rw` | `zoneHomeWrite_right` | theorem (other file) |
| 830 | `rw` | `ZoneContents.words_false` | theorem (other file) |
| 831 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 832 | `rw` | `hl` | local hypothesis |
| 832 | `rw` | `hr` | local hypothesis |
| 832 | `rw` | `List.length_replicate` | core or Mathlib lemma |
| 832 | `rw` | `Fin.val_last` | core or Mathlib lemma |
| 832 | `rw` | `zoneCapacity_eq` | theorem (other file) |
| 836 | `rw` | `ZoneContents.words_false` | theorem (other file) |
| 836 | `rw` | `ZoneContents.words_false` | theorem (other file) |
| 837 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 837 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 838 | `rw` | `hl` | local hypothesis |
| 838 | `rw` | `hr` | local hypothesis |
| 838 | `rw` | `Fin.coe_castSucc` | core or Mathlib lemma |
| 860 | `rwa` | `ZoneContents.words_true` | theorem (other file) |
| 863 | `rwa` | `hr` | local hypothesis |
| 863 | `rwa` | `List.length_nil` | core or Mathlib lemma |
| 863 | `rwa` | `add_zero` | core or Mathlib lemma |
| 866 | `rwa` | `ZoneContents.words_true` | theorem (other file) |
| 877 | `rw` | `zoneRebalance_of_lt` | theorem (other file) |
| 877 | `rw` | `zoneCascade_true` | theorem (other file) |
| 883 | `rw` | `h1` | local hypothesis |
| 883 | `rw` | `h2` | local hypothesis |
| 883 | `rw` | `zoneCapacity_eq` | theorem (other file) |
| 886 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 888 | `rw` | `hjr` | local hypothesis |
| 888 | `rw` | `hjl` | local hypothesis |
| 890 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 893 | `rw` | `hjr` | local hypothesis |
| 897 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 900 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 904 | `rw` | `hfl` | local hypothesis |
| 904 | `rw` | `hfr` | local hypothesis |
| 925 | `rwa` | `ZoneContents.words_false` | theorem (other file) |
| 928 | `rwa` | `hl` | local hypothesis |
| 928 | `rwa` | `List.length_nil` | core or Mathlib lemma |
| 928 | `rwa` | `zero_add` | core or Mathlib lemma |
| 931 | `rwa` | `ZoneContents.words_false` | theorem (other file) |
| 942 | `rw` | `zoneRebalance_of_lt` | theorem (other file) |
| 942 | `rw` | `zoneCascade_false` | theorem (other file) |
| 948 | `rw` | `h1` | local hypothesis |
| 948 | `rw` | `h2` | local hypothesis |
| 948 | `rw` | `zoneCapacity_eq` | theorem (other file) |
| 951 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 953 | `rw` | `hjr` | local hypothesis |
| 953 | `rw` | `hjl` | local hypothesis |
| 955 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 958 | `rw` | `hjr` | local hypothesis |
| 961 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 964 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 968 | `rw` | `hfl` | local hypothesis |
| 968 | `rw` | `hfr` | local hypothesis |
| 985 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 987 | `rwa` | `hr` | local hypothesis |
| 987 | `rwa` | `List.length_nil` | core or Mathlib lemma |
| 987 | `rwa` | `add_zero` | core or Mathlib lemma |
| 989 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 1013 | `rw` | `ZoneContents.words_false` | theorem (other file) |
| 1015 | `rwa` | `hl` | local hypothesis |
| 1015 | `rwa` | `List.length_nil` | core or Mathlib lemma |
| 1015 | `rwa` | `zero_add` | core or Mathlib lemma |
| 1017 | `rw` | `ZoneContents.words_false` | theorem (other file) |
| 1041 | `rw` | `zoneTrackTape_rebalance_left` | theorem (other file) |
| 1044 | `rw` | `zoneTrackTape_rebalance_right` | theorem (other file) |
| 1073 | `rw` | `zoneRebalanceIndex_eq` | theorem (other file) |
| 1074 | `rw` | `zoneRebalanceData_eq` | theorem (other file) |
| 1076 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1079 | `rw` | `Function.update_self` | core or Mathlib lemma |
| 1083 | `rw` | `Function.update_of_ne` | core or Mathlib lemma |
| 1085 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1088 | `rw` | `Function.update_self` | core or Mathlib lemma |
| 1088 | `rw` | `if_pos` | core or Mathlib lemma |
| 1090 | `rw` | `Function.update_of_ne` | core or Mathlib lemma |
| 1090 | `rw` | `if_neg` | core or Mathlib lemma |
| 1092 | `rw` | `zoneTrackStepData_of_lt` | theorem (other file) |
| 1094 | `rw` | `zoneTrackStepData_of_not_lt` | theorem (other file) |
| 1097 | `rw` | `zoneExtendData_eq` | theorem (other file) |
| 1100 | `rw` | `hidx` | local hypothesis |
| 1100 | `rw` | `zoneExtendData_eq` | theorem (other file) |
| 1104 | `rw` | `htape` | local hypothesis |
| 1105 | `rw` | `zoneExtendData_eq` | theorem (other file) |
| 1129 | `rw` | `if_neg` | core or Mathlib lemma |
| 1134 | `rw` | `hDj` | local hypothesis |
| 1136 | `rw` | `show` | core or Mathlib lemma |
| 1136 | `rw` | `hj⟩)` | local hypothesis |
| 1136 | `rw` | `hj⟩` | local hypothesis |
| 1138 | `rw` | `htape` | local hypothesis |
| 1141 | `rw` | `if_neg` | core or Mathlib lemma |
| 1141 | `rw` | `if_pos` | core or Mathlib lemma |
| 1141 | `rw` | `h0` | local hypothesis |
| 1141 | `rw` | `SignType.coe_zero` | core or Mathlib lemma |
| 1141 | `rw` | `add_zero` | core or Mathlib lemma |
| 1144 | `rw` | `if_pos` | core or Mathlib lemma |
| 1144 | `rw` | `if_pos` | core or Mathlib lemma |
| 1145 | `rw` | `if_neg` | core or Mathlib lemma |
| 1145 | `rw` | `if_neg` | core or Mathlib lemma |
| 1150 | `rw` | `htape'` | local hypothesis |
| 1150 | `rw` | `htape` | local hypothesis |
| 1156 | `rw` | `if_neg` | core or Mathlib lemma |
| 1158 | `rw` | `if_pos` | core or Mathlib lemma |
| 1158 | `rw` | `if_pos` | core or Mathlib lemma |
| 1159 | `rw` | `if_neg` | core or Mathlib lemma |
| 1159 | `rw` | `if_neg` | core or Mathlib lemma |
| 1161 | `rw` | `hDj` | local hypothesis |
| 1163 | `rw` | `htape` | local hypothesis |
| 1163 | `rw` | `if_pos` | core or Mathlib lemma |
| 1163 | `rw` | `if_pos` | core or Mathlib lemma |
| 1189 | `rw` | `Cfg.workTapeSymbols_eq` | theorem (other file) |
| 1189 | `rw` | `zoneTrackTape_zero` | theorem (other file) |
| 1189 | `rw` | `h` | local hypothesis |
| 1189 | `rw` | `add_zero` | core or Mathlib lemma |
| 1209 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1210 | `rw` | `tt_rep_home` | own definition/lemma |
| 1215 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1220 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1224 | `rw` | `if_neg` | core or Mathlib lemma |
| 1224 | `rw` | `Function.update_of_ne` | core or Mathlib lemma |
| 1224 | `rw` | `hrep` | local hypothesis |
| 1248 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1251 | `rw` | `hq` | local hypothesis |
| 1266 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1274 | `rw` | `hc` | local hypothesis |
| 1274 | `rw` | `MultiTapeTM.step_of_halt` | theorem (other file) |
| 1275 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1280 | `rw` | `hq` | local hypothesis |
| 1283 | `rw` | `tt_D_succ` | own definition/lemma |
| 1283 | `rw` | `hc` | local hypothesis |
| 1292 | `rw` | `Fin.ext` | core or Mathlib lemma |
| 1301 | `rw` | `Cfg.inputSymbol_of_zero` | theorem (other file) |
| 1301 | `rw` | `h0` | local hypothesis |
| 1302 | `rw` | `h0` | local hypothesis |
| 1306 | `rw` | `h` | local hypothesis |
| 1306 | `rw` | `h1` | local hypothesis |
| 1306 | `rw` | `hlen` | local hypothesis |
| 1307 | `rw` | `Cfg.inputSymbol_of_end` | theorem (other file) |
| 1307 | `rw` | `Cfg.inputSymbol_of_end` | theorem (other file) |
| 1313 | `rw` | `hlen` | local hypothesis |
| 1320 | `rw` | `List.length_map` | core or Mathlib lemma |
| 1365 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1366 | `rw` | `MultiTapeTM.runFrom_zero` | theorem (other file) |
| 1366 | `rw` | `MultiTapeTM.initCfg_eq` | theorem (other file) |
| 1367 | `rw` | `hc` | local hypothesis |
| 1367 | `rw` | `Cfg.init_state` | theorem (other file) |
| 1370 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1371 | `rw` | `zoneCellOfCell_none` | theorem (other file) |
| 1371 | `rw` | `ZoneContents.empty_home` | theorem (other file) |
| 1373 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1375 | `rw` | `Cfg.init_state` | theorem (other file) |
| 1377 | `rw` | `Cfg.init_inputPos` | theorem (other file) |
| 1379 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1380 | `rw` | `hc` | local hypothesis |
| 1380 | `rw` | `Cfg.init_inputPos` | theorem (other file) |
| 1383 | `rw` | `Cfg.init_workTapes` | theorem (other file) |
| 1386 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1390 | `rw` | `Function.update_of_ne` | core or Mathlib lemma |
| 1392 | `rw` | `zoneStart_eq` | theorem (other file) |
| 1396 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1397 | `rw` | `if_neg` | core or Mathlib lemma |
| 1399 | `rw` | `Cfg.init_workTapePos` | theorem (other file) |
| 1401 | `rw` | `Cfg.init_output` | theorem (other file) |
| 1402 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1403 | `rw` | `hc` | local hypothesis |
| 1403 | `rw` | `Cfg.init_output` | theorem (other file) |
| 1403 | `rw` | `List.map_nil` | core or Mathlib lemma |
| 1406 | `rw` | `tt_homeRead` | own definition/lemma |
| 1406 | `rw` | `zonedTape_zero` | theorem (other file) |
| 1406 | `rw` | `zoneCellOfCell_inr` | theorem (other file) |
| 1408 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1409 | `rw` | `hq` | local hypothesis |
| 1415 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1417 | `rw` | `Function.update_eq_self` | core or Mathlib lemma |
| 1418 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1419 | `rw` | `if_neg` | core or Mathlib lemma |
| 1419 | `rw` | `if_neg` | core or Mathlib lemma |
| 1449 | `rw` | `hstep` | local hypothesis |
| 1449 | `rw` | `MultiTapeTM.step_of_some` | theorem (other file) |
| 1449 | `rw` | `hact` | local hypothesis |
| 1451 | `rw` | `hq'` | local hypothesis |
| 1451 | `rw` | `happly` | local hypothesis |
| 1451 | `rw` | `Action.apply_state` | theorem (other file) |
| 1463 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1466 | `rw` | `hq` | local hypothesis |
| 1471 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1472 | `rw` | `hq'` | local hypothesis |
| 1472 | `rw` | `tt_D_succ` | own definition/lemma |
| 1475 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1476 | `rw` | `happly` | local hypothesis |
| 1476 | `rw` | `Action.apply_inputPos` | theorem (other file) |
| 1478 | `rw` | `happly` | local hypothesis |
| 1478 | `rw` | `Action.apply_output` | theorem (other file) |
| 1478 | `rw` | `List.map_append` | core or Mathlib lemma |
| 1478 | `rw` | `tt_output_map` | own definition/lemma |
| 1479 | `rw` | `hstart` | local hypothesis |
| 1479 | `rw` | `hT` | local hypothesis |
| 1479 | `rw` | `hend` | local hypothesis |
| 1515 | `rw` | `hstep` | local hypothesis |
| 1515 | `rw` | `MultiTapeTM.step_of_some` | theorem (other file) |
| 1515 | `rw` | `hact` | local hypothesis |
| 1517 | `rw` | `hh` | local hypothesis |
| 1517 | `rw` | `happly` | local hypothesis |
| 1517 | `rw` | `Action.apply_state` | theorem (other file) |
| 1521 | `rw` | `hstart` | local hypothesis |
| 1523 | `rw` | `H.2` | local hypothesis |
| 1523 | `rw` | `happly` | local hypothesis |
| 1523 | `rw` | `Action.apply_output` | theorem (other file) |
| 1523 | `rw` | `List.map_append` | core or Mathlib lemma |
| 1523 | `rw` | `tt_output_map` | own definition/lemma |
| 1530 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1533 | `rw` | `hq` | local hypothesis |
| 1539 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1541 | `rw` | `MultiTapeTM.initCfg_eq` | theorem (other file) |
| 1541 | `rw` | `phaseHostTM_q₀` | theorem (other file) |
| 1564 | `rw` | `MultiTapeTM.runFrom_zero` | theorem (other file) |
| 1564 | `rw` | `MultiTapeTM.initCfg_eq` | theorem (other file) |
| 1564 | `rw` | `Cfg.init_state` | theorem (other file) |
| 1569 | `rw` | `Nat.add_sub_cancel` | core or Mathlib lemma |
| 1571 | `rw` | `hc` | local hypothesis |
| 1571 | `rw` | `heq` | local hypothesis |
| 1573 | `rw` | `segment_iff` | theorem (other file) |
| 1574 | `rw` | `computesInTime_iff` | theorem (other file) |
| 1574 | `rw` | `tt_HS_init` | own definition/lemma |
| 1575 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1579 | `rw` | `MultiTapeTM.runFrom_add` | theorem (other file) |
| 1579 | `rw` | `hseg.1` | local hypothesis |
| 1581 | `rw` | `h2` | local hypothesis |
| 1581 | `rw` | `hc` | local hypothesis |
| 1581 | `rw` | `heq` | local hypothesis |
| 1581 | `rw` | `ho` | local hypothesis |
| 1606 | `rw` | `Finset.sum_const` | core or Mathlib lemma |
| 1606 | `rw` | `Finset.card_range` | core or Mathlib lemma |
| 1606 | `rw` | `nsmul_eq_mul` | core or Mathlib lemma |
| 1606 | `rw` | `Nat.cast_id` | core or Mathlib lemma |
| 1606 | `rw` | `Nat.mul_comm` | core or Mathlib lemma |
| 1609 | `rw` | `tt_HS_init` | own definition/lemma |
| 1622 | `rw` | `tt_rsum` | own definition/lemma |
| 1622 | `rw` | `Finset.sum_range_succ` | core or Mathlib lemma |
| 1622 | `rw` | `dif_pos` | core or Mathlib lemma |
| 1639 | `rw` | `tt_rsum_succ` | own definition/lemma |
| 1639 | `rw` | `ih` | core or Mathlib lemma |
| 1640 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1642 | `rw` | `ZoneContents.words_false` | theorem (other file) |
| 1644 | `rw` | `he` | local hypothesis |
| 1644 | `rw` | `List.length_nil` | core or Mathlib lemma |
| 1644 | `rw` | `zero_add` | core or Mathlib lemma |
| 1644 | `rw` | `zoneCapacity_eq` | theorem (other file) |
| 1645 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1647 | `rw` | `show` | core or Mathlib lemma |
| 1647 | `rw` | `_⟩).length` | core or Mathlib lemma |
| 1647 | `rw` | `pow_succ` | core or Mathlib lemma |
| 1647 | `rw` | `pow_succ` | core or Mathlib lemma |
| 1648 | `rw` | `pow_succ` | core or Mathlib lemma |
| 1650 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 1651 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1652 | `rw` | `he` | local hypothesis |
| 1673 | `rwa` | `ZoneContents.words_true` | theorem (other file) |
| 1676 | `rwa` | `ZoneContents.words_true` | theorem (other file) |
| 1684 | `rw` | `tt_rsum_succ` | own definition/lemma |
| 1684 | `rw` | `tt_rsum_succ` | own definition/lemma |
| 1686 | `rw` | `ih₁` | core or Mathlib lemma |
| 1686 | `rw` | (hlow | core or Mathlib lemma |
| 1686 | `rw` | `by` | core or Mathlib lemma |
| 1687 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1689 | `rw` | `pow_succ` | core or Mathlib lemma |
| 1692 | `rw` | (hframe | core or Mathlib lemma |
| 1692 | `rw` | `by` | core or Mathlib lemma |
| 1692 | `rw` | `ih₂` | core or Mathlib lemma |
| 1705 | `rw` | `zoneRebalance_of_lt` | theorem (other file) |
| 1705 | `rw` | `zoneCascade_true` | theorem (other file) |
| 1707 | `rw` | `hz0` | local hypothesis |
| 1708 | `rw` | `hfin` | local hypothesis |
| 1708 | `rw` | `ih₁` | core or Mathlib lemma |
| 1708 | `rw` | `hnj` | local hypothesis |
| 1708 | `rw` | `hz0'` | local hypothesis |
| 1708 | `rw` | `hj'` | local hypothesis |
| 1731 | `rwa` | `ZoneContents.words_false` | theorem (other file) |
| 1734 | `rwa` | `ZoneContents.words_false` | theorem (other file) |
| 1742 | `rw` | `tt_rsum_succ` | own definition/lemma |
| 1742 | `rw` | `tt_rsum_succ` | own definition/lemma |
| 1744 | `rw` | `ih₁` | core or Mathlib lemma |
| 1744 | `rw` | (hlow | core or Mathlib lemma |
| 1744 | `rw` | `by` | core or Mathlib lemma |
| 1745 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1747 | `rw` | `pow_succ` | core or Mathlib lemma |
| 1750 | `rw` | (hframe | core or Mathlib lemma |
| 1750 | `rw` | `by` | core or Mathlib lemma |
| 1750 | `rw` | `ih₂` | core or Mathlib lemma |
| 1764 | `rw` | `zoneRebalance_of_lt` | theorem (other file) |
| 1764 | `rw` | `zoneCascade_false` | theorem (other file) |
| 1766 | `rw` | `hz0` | local hypothesis |
| 1767 | `rw` | `hfin` | local hypothesis |
| 1767 | `rw` | `ih₁` | core or Mathlib lemma |
| 1767 | `rw` | `hnj` | local hypothesis |
| 1767 | `rw` | `hz0'` | local hypothesis |
| 1767 | `rw` | `hj'` | local hypothesis |
| 1769 | `rw` | `pow_succ` | core or Mathlib lemma |
| 1776 | `simp only` | `zoneHomeWrite_right` | theorem (other file) |
| 1787 | `rw` | `dif_pos` | core or Mathlib lemma |
| 1787 | `rw` | `dif_pos` | core or Mathlib lemma |
| 1789 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 1789 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 1792 | `rw` | `tt_rsum_succ` | own definition/lemma |
| 1792 | `rw` | `hold` | local hypothesis |
| 1794 | `rw` | `ZoneContents.words_true` | theorem (other file) |
| 1837 | `rw` | `h2` | local hypothesis |
| 1839 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1843 | `rw` | `h2` | local hypothesis |
| 1845 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1847 | `rw` | `zoneRebalanceIndex_eq` | theorem (other file) |
| 1849 | `rwa` | `zoneRebalanceIndex_eq` | theorem (other file) |
| 1850 | `rw` | `zoneTrackStepData_of_lt` | theorem (other file) |
| 1850 | `rw` | `zoneRebalanceData_eq` | theorem (other file) |
| 1851 | `simp only` | `if_pos` | core or Mathlib lemma |
| 1851 | `simp only` | `Function.update_self` | core or Mathlib lemma |
| 1854 | `rw` | (hreb | core or Mathlib lemma |
| 1854 | `rw` | `add_zero` | core or Mathlib lemma |
| 1855 | `rw` | `Function.update_of_ne` | core or Mathlib lemma |
| 1855 | `rw` | `add_zero` | core or Mathlib lemma |
| 1857 | `rwa` | `zoneRebalanceIndex_eq` | theorem (other file) |
| 1863 | `rw` | `hidx'` | local hypothesis |
| 1865 | `rw` | `zoneTrackStepData_of_not_lt` | theorem (other file) |
| 1865 | `rw` | `zoneRebalanceData_eq` | theorem (other file) |
| 1865 | `rw` | `zoneExtendData_eq` | theorem (other file) |
| 1866 | `simp only` | `if_neg` | core or Mathlib lemma |
| 1866 | `simp only` | `Function.update_self` | core or Mathlib lemma |
| 1867 | `rw` | `hidx'` | local hypothesis |
| 1868 | `rw` | `hidx` | local hypothesis |
| 1869 | `rw` | (hreb | core or Mathlib lemma |
| 1873 | `rw` | `Function.update_of_ne` | core or Mathlib lemma |
| 1887 | `rw` | `show` | core or Mathlib lemma |
| 1887 | `rw` | `h⟩)` | local hypothesis |
| 1887 | `rw` | `h⟩` | local hypothesis |
| 1889 | `rw` | `show` | core or Mathlib lemma |
| 1889 | `rw` | `h⟩)` | local hypothesis |
| 1889 | `rw` | `h⟩` | local hypothesis |
| 1894 | `rw` | `zoneTrackStepData_of_lt` | theorem (other file) |
| 1894 | `rw` | `zoneRebalanceData_eq` | theorem (other file) |
| 1895 | `rw` | `zoneTrackStepData_of_not_lt` | theorem (other file) |
| 1895 | `rw` | `zoneRebalanceData_eq` | theorem (other file) |
| 1895 | `rw` | `zoneExtendData_eq` | theorem (other file) |
| 1897 | `rw` | `show` | core or Mathlib lemma |
| 1900 | `change` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 1910 | `rw` | `ih` | core or Mathlib lemma |
| 1913 | `rw` | `show` | core or Mathlib lemma |
| 1913 | `rw` | `h⟩)` | local hypothesis |
| 1913 | `rw` | `h⟩` | local hypothesis |
| 1915 | `rw` | `show` | core or Mathlib lemma |
| 1915 | `rw` | `h⟩)` | local hypothesis |
| 1915 | `rw` | `h⟩` | local hypothesis |
| 1918 | `rw` | `he` | local hypothesis |
| 1920 | `rw` | `show` | core or Mathlib lemma |
| 1965 | `rw` | `hE` | local hypothesis |
| 1965 | `rw` | `tt_Dtr_other` | own definition/lemma |
| 1973 | `rw` | `hidx` | local hypothesis |
| 1974 | `rw` | `show` | core or Mathlib lemma |
| 1976 | `rw` | `hH1` | local hypothesis |
| 1976 | `rw` | `hi0` | local hypothesis |
| 1977 | `rw` | `hD'r` | local hypothesis |
| 1980 | `rw` | `hidx` | local hypothesis |
| 1981 | `rw` | `show` | core or Mathlib lemma |
| 1985 | `rw` | `hH1` | local hypothesis |
| 1986 | `rw` | `hi` | local hypothesis |
| 1989 | `rw` | `hD'r` | local hypothesis |
| 1989 | `rw` | `hown` | local hypothesis |
| 1991 | `rw` | `hEr` | local hypothesis |
| 1992 | `rw` | `hi` | local hypothesis |
| 1992 | `rw` | `zoneRebalanceIndex_eq` | theorem (other file) |
| 1995 | `rw` | `hdir` | local hypothesis |
| 1995 | `rw` | `if_neg` | core or Mathlib lemma |
| 1997 | `rw` | `hdir` | local hypothesis |
| 1997 | `rw` | `if_pos` | core or Mathlib lemma |
| 1999 | `rw` | `hi` | local hypothesis |
| 2001 | `rw` | `hD'r` | local hypothesis |
| 2001 | `rw` | `hown` | local hypothesis |
| 2001 | `rw` | `c2` | core or Mathlib lemma |
| 2001 | `rw` | `hEr` | local hypothesis |
| 2002 | `simp` | `tt_shift` | own definition/lemma |
| 2003 | `rw` | `hs` | local hypothesis |
| 2004 | `rw` | `hi` | local hypothesis |
| 2059 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 2062 | `rw` | `hq` | local hypothesis |
| 2063 | `rw` | `tt_D_succ` | own definition/lemma |
| 2063 | `rw` | `hidx` | local hypothesis |
| 2083 | `rw` | `Finset.mem_range` | core or Mathlib lemma |
| 2100 | `rw` | `hVa` | local hypothesis |
| 2108 | `rw` | ((F | core or Mathlib lemma |
| 2118 | `rw` | `hn` | local hypothesis |
| 2118 | `rw` | `pow_succ` | core or Mathlib lemma |
| 2120 | `rw` | `hb` | local hypothesis |
| 2126 | `rw` | `hb` | local hypothesis |
| 2161 | `rw` | `if_neg` | core or Mathlib lemma |
| 2161 | `rw` | `add_zero` | core or Mathlib lemma |
| 2162 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 2163 | `rw` | `tt_rsum_homeWrite` | own definition/lemma |
| 2173 | `rw` | `show` | core or Mathlib lemma |
| 2173 | `rw` | `hj⟩)` | local hypothesis |
| 2173 | `rw` | `hj⟩` | local hypothesis |
| 2175 | `rw` | `ih₁` | core or Mathlib lemma |
| 2178 | `rw` | `if_pos` | core or Mathlib lemma |
| 2178 | `rw` | `if_neg` | core or Mathlib lemma |
| 2178 | `rw` | `h0` | local hypothesis |
| 2182 | `rw` | `if_pos` | core or Mathlib lemma |
| 2182 | `rw` | `if_pos` | core or Mathlib lemma |
| 2183 | `rw` | `if_neg` | core or Mathlib lemma |
| 2183 | `rw` | `if_neg` | core or Mathlib lemma |
| 2191 | `rw` | `c5` | core or Mathlib lemma |
| 2198 | `rw` | `c3` | core or Mathlib lemma |
| 2198 | `rw` | `hℓ` | local hypothesis |
| 2198 | `rw` | `if_pos` | core or Mathlib lemma |
| 2198 | `rw` | `hsh` | local hypothesis |
| 2200 | `rw` | `if_neg` | core or Mathlib lemma |
| 2200 | `rw` | `add_zero` | core or Mathlib lemma |
| 2204 | `rw` | `c4'` | core or Mathlib lemma |
| 2204 | `rw` | `hℓ` | local hypothesis |
| 2209 | `rw` | `if_pos` | core or Mathlib lemma |
| 2209 | `rw` | `if_pos` | core or Mathlib lemma |
| 2210 | `rw` | `if_neg` | core or Mathlib lemma |
| 2210 | `rw` | `if_neg` | core or Mathlib lemma |
| 2211 | `rw` | `hif` | local hypothesis |
| 2214 | `rw` | `c5` | core or Mathlib lemma |
| 2219 | `rw` | `zoneRebalanceIndex_eq` | theorem (other file) |
| 2223 | `rw` | `if_neg` | core or Mathlib lemma |
| 2223 | `rw` | `add_zero` | core or Mathlib lemma |
| 2228 | `rw` | `hdir` | local hypothesis |
| 2228 | `rw` | `if_neg` | core or Mathlib lemma |
| 2229 | `rw` | `hl` | local hypothesis |
| 2234 | `rw` | `hdir` | local hypothesis |
| 2234 | `rw` | `if_pos` | core or Mathlib lemma |
| 2235 | `rw` | `hl` | local hypothesis |
| 2239 | `rw` | `pow_succ` | core or Mathlib lemma |
| 2241 | `rw` | `show` | core or Mathlib lemma |
| 2243 | `rw` | `ih₁` | core or Mathlib lemma |
| 2243 | `rw` | `if_pos` | core or Mathlib lemma |
| 2243 | `rw` | `if_pos` | core or Mathlib lemma |
| 2247 | `rw` | `if_pos` | core or Mathlib lemma |
| 2248 | `rw` | `add_assoc` | core or Mathlib lemma |
| 2264 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 2266 | `rw` | `MultiTapeTM.runFrom_zero` | theorem (other file) |
| 2266 | `rw` | `MultiTapeTM.initCfg_eq` | theorem (other file) |
| 2266 | `rw` | `Cfg.init_workTapePos` | theorem (other file) |
| 2274 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 2277 | `rw` | `hq` | local hypothesis |
| 2278 | `rw` | `hD` | local hypothesis |
| 2278 | `rw` | `hc` | local hypothesis |
| 2278 | `rw` | `MultiTapeTM.step_of_halt` | theorem (other file) |
| 2287 | `rw` | `MultiTapeTM.initCfg_eq` | theorem (other file) |
| 2287 | `rw` | `Cfg.init_workTapePos` | theorem (other file) |
| 2287 | `rw` | `Finset.mem_Icc` | core or Mathlib lemma |
| 2291 | `rw` | `tt_D_succ` | own definition/lemma |
| 2293 | `rw` | `hc` | local hypothesis |
| 2293 | `rw` | `MultiTapeTM.step_of_some` | theorem (other file) |
| 2293 | `rw` | `Action.apply_workTapePos` | theorem (other file) |
| 2293 | `rw` | `hact` | local hypothesis |
| 2313 | `rw` | `pow_succ` | core or Mathlib lemma |
| 2344 | `rw` | `Nat.add_sub_cancel` | core or Mathlib lemma |
| 2344 | `rw` | `Finset.sum_range_succ` | core or Mathlib lemma |
| 2359 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 2362 | `rw` | `hq` | local hypothesis |
| 2366 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |
| 2369 | `rw` | `hq` | local hypothesis |
| 2370 | `rw` | `hT` | local hypothesis |
| 2380 | `rw` | `hidx` | local hypothesis |
| 2383 | `rw` | `Finset.sum_add_distrib` | core or Mathlib lemma |
| 2383 | `rw` | `Finset.mul_sum` | core or Mathlib lemma |
| 2398 | `rw` | `hL` | local hypothesis |
| 2398 | `rw` | `pow_succ` | core or Mathlib lemma |
| 2399 | `show` | (a `show`/`change` goal: reduces only this file's own definitions and structure projections; confirmed by the seal) | — |

Other-file definitions passed to a rewriting tactic: 0
