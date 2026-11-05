| line | tactic | argument | origin |
|---|---|---|---|
| 707 | `simp` | `(no arguments)` | default simp set / closing |
| 997 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 997 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 999 | `rw` | `hs` | local hypothesis/term |
| 1000 | `rw` | `Cfg.mapState_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1000 | `rw` | `Cfg.mapState_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1001 | `rw` | `Cfg.mapState_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1001 | `rw` | `Cfg.mapState_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1002 | `rw` | `Cfg.mapState_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1002 | `rw` | `Cfg.mapState_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1003 | `rw` | `Cfg.mapState_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1003 | `rw` | `Cfg.mapState_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1009 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1052 | `simp only` | `List.length_nil` | core thm (Init.Data.List.Basic) |
| 1052 | `simp only` | `Nat.cast_zero` | Mathlib thm (Mathlib.Data.Nat.Cast.Defs) |
| 1054 | `rw` | `(no arguments)` | default simp set / closing |
| 1066 | `simp` | `(no arguments)` | default simp set / closing |
| 1067 | `rw` | `MultiTapeTM.runFrom_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1067 | `rw` | `hst` | local hypothesis/term |
| 1072 | `simp` | `hc₁` | local hypothesis/term |
| 1078 | `simp only` | `hc₂` | local hypothesis/term |
| 1078 | `simp only` | `hc₁` | local hypothesis/term |
| 1078 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1078 | `simp only` | `List.length_nil` | core thm (Init.Data.List.Basic) |
| 1078 | `simp only` | `Nat.cast_zero` | Mathlib thm (Mathlib.Data.Nat.Cast.Defs) |
| 1078 | `simp only` | `hpos` | local hypothesis/term |
| 1079 | `rw` | `htape` | local hypothesis/term |
| 1098 | `simp` | `(no arguments)` | default simp set / closing |
| 1100 | `rw` | `e` | local hypothesis/term |
| 1100 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1101 | `unfold` | `nf_V` | own (this file) |
| 1102 | `rw` | `hA` | local hypothesis/term |
| 1102 | `rw` | `hre` | local hypothesis/term |
| 1104 | `simp` | `hc₃` | local hypothesis/term |
| 1105 | `simp only` | `hc₃` | local hypothesis/term |
| 1105 | `simp only` | `hc₂` | local hypothesis/term |
| 1105 | `simp only` | `hc₁` | local hypothesis/term |
| 1105 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1105 | `simp only` | `List.length_nil` | core thm (Init.Data.List.Basic) |
| 1105 | `simp only` | `Nat.cast_zero` | Mathlib thm (Mathlib.Data.Nat.Cast.Defs) |
| 1105 | `simp only` | `hpos` | local hypothesis/term |
| 1107 | `simp only` | `hc₃` | local hypothesis/term |
| 1107 | `simp only` | `hc₂` | local hypothesis/term |
| 1107 | `simp only` | `hc₁` | local hypothesis/term |
| 1108 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1108 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1109 | `simp only` | `hc₃` | local hypothesis/term |
| 1109 | `simp only` | `hc₂` | local hypothesis/term |
| 1109 | `simp only` | `hc₁` | local hypothesis/term |
| 1110 | `simp only` | `hc₃` | local hypothesis/term |
| 1110 | `simp only` | `hc₂` | local hypothesis/term |
| 1110 | `simp only` | `hc₁` | local hypothesis/term |
| 1111 | `simp only` | `hc₃` | local hypothesis/term |
| 1111 | `simp only` | `hc₂` | local hypothesis/term |
| 1111 | `simp only` | `hc₁` | local hypothesis/term |
| 1113 | `unfold` | `nf_V` | own (this file) |
| 1115 | `rw` | `hpA u hu1` | local hypothesis/term |
| 1119 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1119 | `rw` | `hA` | local hypothesis/term |
| 1119 | `rw` | `hre` | local hypothesis/term |
| 1119 | `rw` | `hpB v (by simp at hu ⊢; omega)` | local hypothesis/term |
| 1155 | `rw` | `List.length_drop` | core thm (Init.Data.List.TakeDrop) |
| 1161 | `rw` | `show c.workTapePos 1 - i + (p + i) = c.workTapePos 1 + p by ring` | local hypothesis/term |
| 1162 | `rw` | `h` | local hypothesis/term |
| 1164 | `rw` | `(no arguments)` | default simp set / closing |
| 1183 | `simp` | `hc₁` | local hypothesis/term |
| 1189 | `simp only` | `hc₂` | local hypothesis/term |
| 1189 | `simp only` | `hc₁` | local hypothesis/term |
| 1189 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1190 | `rw` | `← htape p h0 h1` | local hypothesis/term |
| 1192 | `rw` | `hdl` | local hypothesis/term |
| 1209 | `simp only` | `hc₃` | local hypothesis/term |
| 1209 | `simp only` | `hc₂` | local hypothesis/term |
| 1209 | `simp only` | `hc₁` | local hypothesis/term |
| 1209 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1210 | `rw` | `hdl` | local hypothesis/term |
| 1214 | `simp` | `hc₃` | local hypothesis/term |
| 1222 | `simp only` | `hc₄` | local hypothesis/term |
| 1223 | `rw` | `e` | local hypothesis/term |
| 1224 | `simp only` | `hc₄` | local hypothesis/term |
| 1224 | `simp only` | `hc₃` | local hypothesis/term |
| 1224 | `simp only` | `hc₂` | local hypothesis/term |
| 1224 | `simp only` | `hc₁` | local hypothesis/term |
| 1243 | `rw` | `List.length_drop` | core thm (Init.Data.List.TakeDrop) |
| 1245 | `rw` | `e` | local hypothesis/term |
| 1245 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1246 | `unfold` | `nf_V` | own (this file) |
| 1247 | `rw` | `hA` | local hypothesis/term |
| 1247 | `rw` | `hre` | local hypothesis/term |
| 1247 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1247 | `rw` | `hB` | local hypothesis/term |
| 1247 | `rw` | `hre2` | local hypothesis/term |
| 1249 | `simp` | `hc₅` | local hypothesis/term |
| 1250 | `simp only` | `hc₅` | local hypothesis/term |
| 1250 | `simp only` | `hc₄` | local hypothesis/term |
| 1252 | `simp only` | `hc₅` | local hypothesis/term |
| 1252 | `simp only` | `hc₄` | local hypothesis/term |
| 1252 | `simp only` | `hc₃` | local hypothesis/term |
| 1252 | `simp only` | `hc₂` | local hypothesis/term |
| 1252 | `simp only` | `hc₁` | local hypothesis/term |
| 1253 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1253 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1254 | `simp only` | `hc₅` | local hypothesis/term |
| 1254 | `simp only` | `hc₄` | local hypothesis/term |
| 1254 | `simp only` | `hc₃` | local hypothesis/term |
| 1254 | `simp only` | `hc₂` | local hypothesis/term |
| 1254 | `simp only` | `hc₁` | local hypothesis/term |
| 1256 | `rw` | `if_neg (fun h => absurd h.1 (by decide))` | core thm (Init.Core) |
| 1257 | `simp only` | `hc₅` | local hypothesis/term |
| 1257 | `simp only` | `hc₄` | local hypothesis/term |
| 1257 | `simp only` | `hc₃` | local hypothesis/term |
| 1257 | `simp only` | `hc₂` | local hypothesis/term |
| 1257 | `simp only` | `hc₁` | local hypothesis/term |
| 1258 | `simp only` | `hc₅` | local hypothesis/term |
| 1258 | `simp only` | `hc₄` | local hypothesis/term |
| 1258 | `simp only` | `hc₃` | local hypothesis/term |
| 1258 | `simp only` | `hc₂` | local hypothesis/term |
| 1258 | `simp only` | `hc₁` | local hypothesis/term |
| 1260 | `simp only` | `hc₄` | local hypothesis/term |
| 1261 | `simp only` | `hc₄` | local hypothesis/term |
| 1261 | `simp only` | `hc₃` | local hypothesis/term |
| 1261 | `simp only` | `hc₂` | local hypothesis/term |
| 1261 | `simp only` | `hc₁` | local hypothesis/term |
| 1264 | `rw` | `hq` | local hypothesis/term |
| 1264 | `rw` | `e4` | local hypothesis/term |
| 1264 | `rw` | `ew` | local hypothesis/term |
| 1266 | `rw` | `if_pos ⟨rfl` | core thm (Init.Core) |
| 1266 | `rw` | `h⟩` | local hypothesis/term |
| 1266 | `rw` | `if_pos h` | core thm (Init.Core) |
| 1267 | `rw` | `if_neg (fun h' => h h'.2)` | core thm (Init.Core) |
| 1267 | `rw` | `if_neg h` | core thm (Init.Core) |
| 1269 | `unfold` | `nf_V` | own (this file) |
| 1271 | `rw` | `hpA u hu1` | local hypothesis/term |
| 1275 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1275 | `rw` | `hA` | local hypothesis/term |
| 1275 | `rw` | `hre` | local hypothesis/term |
| 1277 | `rw` | `hpB v hv1` | local hypothesis/term |
| 1280 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1280 | `rw` | `hB` | local hypothesis/term |
| 1280 | `rw` | `hre2` | local hypothesis/term |
| 1280 | `rw` | `hpC w (by rw [List.length_drop] at hu; omega)` | local hypothesis/term |
| 1293 | `rw` | `MultiTapeTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1295 | `rw` | `guessRunCfg_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1295 | `rw` | `streamStartCfg_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1296 | `rw` | `guessRunCfg_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1296 | `rw` | `streamStartCfg_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1296 | `rw` | `Cfg.init_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1298 | `rw` | `guessRunCfg_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1298 | `rw` | `streamStartCfg_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1298 | `rw` | `Cfg.init_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1301 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1301 | `rw` | `if_pos rfl` | core thm (Init.Core) |
| 1303 | `rw` | `if_pos hp` | core thm (Init.Core) |
| 1303 | `rw` | `sub_zero` | Mathlib thm (Mathlib.Algebra.Group.Basic) |
| 1304 | `rw` | `if_neg hp` | core thm (Init.Core) |
| 1304 | `rw` | `Cfg.init_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1306 | `rw` | `FinTM.bufferTape_of_neg s hneg` | TCSlib thm (TCSlib.Complexity.TuringMachine.Simulation) |
| 1307 | `rw` | `FinTM.bufferTape_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Simulation) |
| 1307 | `rw` | `if_pos (by omega)` | core thm (Init.Core) |
| 1309 | `rw` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1309 | `rw` | `if_neg hi` | core thm (Init.Core) |
| 1309 | `rw` | `Cfg.init_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1311 | `rw` | `guessRunCfg_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1311 | `rw` | `streamStartCfg_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1311 | `rw` | `Cfg.init_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1312 | `rw` | `guessRunCfg_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1312 | `rw` | `streamStartCfg_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1312 | `rw` | `Cfg.init_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1320 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1320 | `rw` | `streamStartCfg_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1320 | `rw` | `streamStartCfg_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1321 | `rw` | `Cfg.mapState_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1321 | `rw` | `streamStartCfg_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1321 | `rw` | `streamStartCfg_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1322 | `rw` | `Cfg.mapState_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1322 | `rw` | `streamStartCfg_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1322 | `rw` | `streamStartCfg_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1323 | `rw` | `Cfg.mapState_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1323 | `rw` | `streamStartCfg_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1323 | `rw` | `streamStartCfg_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1324 | `rw` | `Cfg.mapState_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 1324 | `rw` | `streamStartCfg_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1324 | `rw` | `streamStartCfg_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 1332 | `rw` | `← h` | local hypothesis/term |
| 1333 | `rw` | `Cfg.inputSymbol_of_zero (Fin.ext h0)` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1333 | `rw` | `Cfg.inputSymbol_of_zero h0'` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1335 | `rw` | `Cfg.inputSymbol_of_end he` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1335 | `rw` | `Cfg.inputSymbol_of_end (by omega)` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1337 | `rw` | `(no arguments)` | default simp set / closing |
| 1358 | `rw` | `← hσ` | local hypothesis/term |
| 1359 | `rw` | `hp]` | local hypothesis/term |
| 1359 | `rw` | `by rw [hp` | local hypothesis/term |
| 1360 | `rw` | `hp` | local hypothesis/term |
| 1364 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1367 | `rw` | `Function.update_of_ne he` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1368 | `show` | `(if p.val < 2 * N.k + 3 then some (rec p) else none) = some (rec p)` | goal restatement (own statement form; no unfolding of other files) |
| 1369 | `rw` | `if_pos (by omega)` | core thm (Init.Core) |
| 1371 | `rw` | `List.ofFn_succ_last` | core thm (Init.Data.List.OfFn) |
| 1371 | `rw` | `List.foldl_append` | core thm (Init.Data.List.Lemmas) |
| 1371 | `rw` | `List.foldl_cons` | core thm (Init.Data.List.Basic) |
| 1371 | `rw` | `List.foldl_nil` | core thm (Init.Data.List.Basic) |
| 1372 | `rw` | `hσ` | local hypothesis/term |
| 1392 | `rw` | `MultiTapeTM.runFrom_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1394 | `rw` | `hst` | local hypothesis/term |
| 1399 | `show` | `d.workTapePos i = Function.update d.workTapePos 0 (d.workTapePos 0 + ((0 : ℕ) : ℤ)) i` | goal restatement (own statement form; no unfolding of other files) |
| 1400 | `rw` | `Nat.cast_zero` | Mathlib thm (Mathlib.Data.Nat.Cast.Defs) |
| 1400 | `rw` | `add_zero` | Mathlib thm (Mathlib.Algebra.Group.Defs) |
| 1400 | `rw` | `Function.update_eq_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1403 | `rw` | `MultiTapeTM.runFrom_succ_eq_step'` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1403 | `rw` | `nf_leaf_prefix N j d rec ctl hst hA m (by omega)` | own (this file) |
| 1406 | `rw` | `hp` | local hypothesis/term |
| 1412 | `rw` | `Cfg.workTapeSymbols_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1413 | `show` | `d.workTapes 0 (Function.update d.workTapePos 0 (d.workTapePos 0 + m) 0) = _` | goal restatement (own statement form; no unfolding of other files) |
| 1414 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1416 | `rw` | `(no arguments)` | default simp set / closing |
| 1417 | `simp only` | `nf_leaf` | own (this file) |
| 1418 | `rw` | `if_neg (by rw [hm1]; omega), hsym, Option.getD_some])` | core thm (Init.Core) |
| 1420 | `show` | `some (nf_LeafSt.read (nf_sweepStep N _ _)) = some (nf_LeafSt.read` | goal restatement (own statement form; no unfolding of other files) |
| 1423 | `rw` | `List.ofFn_succ_last` | core thm (Init.Data.List.OfFn) |
| 1423 | `rw` | `List.foldl_append` | core thm (Init.Data.List.Lemmas) |
| 1424 | `simp only` | `Fin.coe_castSucc` | core/Mathlib lemma (applied definitionally by simp: no constant left in the term) |
| 1424 | `simp only` | `Fin.val_last` | core/Mathlib lemma (applied definitionally by simp: no constant left in the term) |
| 1424 | `simp only` | `List.foldl_cons` | core thm (Init.Data.List.Basic) |
| 1424 | `simp only` | `List.foldl_nil` | core thm (Init.Data.List.Basic) |
| 1424 | `simp only` | `hp` | local hypothesis/term |
| 1428 | `dsimp only` | `(no arguments)` | default simp set / closing |
| 1431 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1431 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1431 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1431 | `rw` | `SignType.coe_one` | Mathlib thm (Mathlib.Data.Sign.Defs) |
| 1434 | `rw` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1434 | `rw` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1434 | `rw` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1463 | `rw` | `hpre u hu` | local hypothesis/term |
| 1470 | `rw` | `(no arguments)` | default simp set / closing |
| 1472 | `rw` | `Cfg.workTapeSymbols_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1473 | `show` | `d.workTapes 0 (Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) 0) = ` | goal restatement (own statement form; no unfolding of other files) |
| 1474 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1510 | `rw` | `(no arguments)` | default simp set / closing |
| 1511 | `simp only` | `nf_leaf` | own (this file) |
| 1512 | `rw` | `if_pos h1` | core thm (Init.Core) |
| 1512 | `rw` | `h2` | local hypothesis/term |
| 1512 | `rw` | `hq` | local hypothesis/term |
| 1513 | `dsimp only` | `(no arguments)` | default simp set / closing |
| 1514 | `rw` | `hsym, Option.getD_some, h3, hinp, if_pos hdec])` | local hypothesis/term |
| 1516 | `show` | `some (if rec ⟨2 * N.k + 3, by omega⟩ then nf_LeafSt.pass` | goal restatement (own statement form; no unfolding of other files) |
| 1518 | `rw` | `h4` | local hypothesis/term |
| 1524 | `simp only` | `hc` | local hypothesis/term |
| 1524 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1524 | `simp only` | `SignType.coe_one` | Mathlib thm (Mathlib.Data.Sign.Defs) |
| 1527 | `simp only` | `hc` | local hypothesis/term |
| 1527 | `simp only` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1529 | `rw` | `hrun` | local hypothesis/term |
| 1531 | `rw` | `(no arguments)` | default simp set / closing |
| 1532 | `simp only` | `nf_leaf` | own (this file) |
| 1533 | `rw` | `if_pos h1, h2, hn])` | core thm (Init.Core) |
| 1536 | `rw` | `(no arguments)` | default simp set / closing |
| 1537 | `simp only` | `nf_leaf` | own (this file) |
| 1538 | `rw` | `if_pos h1, h2, hq])` | core thm (Init.Core) |
| 1540 | `rw` | `(no arguments)` | default simp set / closing |
| 1541 | `simp only` | `nf_leaf` | own (this file) |
| 1542 | `rw` | `if_pos h1` | core thm (Init.Core) |
| 1542 | `rw` | `h2` | local hypothesis/term |
| 1542 | `rw` | `hq` | local hypothesis/term |
| 1543 | `dsimp only` | `(no arguments)` | default simp set / closing |
| 1544 | `rw` | `hsym, Option.getD_some, h3, hinp, if_neg hdec])` | local hypothesis/term |
| 1569 | `simp only` | `(no arguments)` | default simp set / closing |
| 1572 | `simp only` | `nf_complete` | own (this file) |
| 1572 | `simp only` | `nf_vstep` | own (this file) |
| 1572 | `simp only` | `hc` | local hypothesis/term |
| 1574 | `simp only` | `nf_complete` | own (this file) |
| 1574 | `simp only` | `nf_vstep` | own (this file) |
| 1574 | `simp only` | `hc` | local hypothesis/term |
| 1590 | `simp only` | `(no arguments)` | default simp set / closing |
| 1593 | `simp only` | `nf_complete` | own (this file) |
| 1593 | `simp only` | `nf_vstep` | own (this file) |
| 1593 | `simp only` | `hc` | local hypothesis/term |
| 1595 | `simp only` | `nf_complete` | own (this file) |
| 1595 | `simp only` | `nf_vstep` | own (this file) |
| 1595 | `simp only` | `hc` | local hypothesis/term |
| 1596 | `rw` | `Action.apply_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1596 | `rw` | `StepBlock.outputSummary_append` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.StepBlock) |
| 1625 | `rw` | `List.flatMap_cons` | core thm (Init.Data.List.Basic) |
| 1628 | `rw` | `List.length_append` | core thm (Init.Data.List.Basic) |
| 1628 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 1629 | `rw` | `hT p.val hlt` | local hypothesis/term |
| 1629 | `rw` | `List.getElem?_append_left (by rw [List.length_ofFn` | core thm (Init.Data.List.Lemmas) |
| 1631 | `simp` | `(no arguments)` | default simp set / closing |
| 1633 | `rw` | `List.length_append` | core thm (Init.Data.List.Basic) |
| 1633 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 1635 | `rw` | `List.getElem?_append_right (by rw [List.length_ofFn` | core thm (Init.Data.List.Lemmas) |
| 1637 | `rw` | `← e` | local hypothesis/term |
| 1653 | `simp` | `(no arguments)` | default simp set / closing |
| 1657 | `simp` | `(no arguments)` | default simp set / closing |
| 1668 | `simp` | `(no arguments)` | default simp set / closing |
| 1669 | `simp only` | `List.getElem_cons_zero` | core/Mathlib lemma (applied definitionally by simp: no constant left in the term) |
| 1669 | `simp only` | `List.length_cons` | core thm (Init.Data.List.Basic) |
| 1669 | `simp only` | `zero_add` | Mathlib thm (Mathlib.Algebra.Group.Defs) |
| 1670 | `rw` | `this` | local hypothesis/term |
| 1671 | `simp` | `(no arguments)` | default simp set / closing |
| 1672 | `simp` | `(no arguments)` | default simp set / closing |
| 1673 | `simpa` | `(no arguments)` | default simp set / closing |
| 1711 | `rw` | `hip` | local hypothesis/term |
| 1718 | `rw` | `hinp` | local hypothesis/term |
| 1718 | `rw` | `hdec` | local hypothesis/term |
| 1722 | `simpa` | `(no arguments)` | default simp set / closing |
| 1723 | `simp` | `(no arguments)` | default simp set / closing |
| 1726 | `rw` | `hrun` | local hypothesis/term |
| 1726 | `rw` | `if_pos hl` | core thm (Init.Core) |
| 1727 | `simp` | `(no arguments)` | default simp set / closing |
| 1729 | `simp` | `(no arguments)` | default simp set / closing |
| 1733 | `simpa` | `(no arguments)` | default simp set / closing |
| 1734 | `rw` | `if_neg (by simp [hl])` | core thm (Init.Core) |
| 1743 | `show` | `moveInputPos d.inputPos _ = _` | goal restatement (own statement form; no unfolding of other files) |
| 1744 | `simp only` | `nf_vstep` | own (this file) |
| 1744 | `simp only` | `hq` | local hypothesis/term |
| 1745 | `rw` | `Action.apply_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1745 | `rw` | `hip` | local hypothesis/term |
| 1749 | `show` | `d.workTapes 0 (Function.update d.workTapePos 0` | goal restatement (own statement form; no unfolding of other files) |
| 1751 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1754 | `simp` | `(no arguments)` | default simp set / closing |
| 1760 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1760 | `rw` | `hrun` | local hypothesis/term |
| 1763 | `rw` | `hT` | local hypothesis/term |
| 1763 | `simp` | `(no arguments)` | default simp set / closing |
| 1764 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1764 | `rw` | `hrun` | local hypothesis/term |
| 1764 | `rw` | `hcfg` | local hypothesis/term |
| 1772 | `simp only` | `hd'` | local hypothesis/term |
| 1772 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1772 | `simp only` | `List.length_cons` | core thm (Init.Data.List.Basic) |
| 1775 | `simp only` | `hd'` | local hypothesis/term |
| 1775 | `simp only` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1780 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1780 | `rw` | `hrun` | local hypothesis/term |
| 1786 | `rw` | `hdec` | local hypothesis/term |
| 1786 | `rw` | `hinp` | local hypothesis/term |
| 1801 | `change` | `, and there is no exit before.` | goal restatement (own statement form; no unfolding of other files) |
| 1839 | `rw` | `(no arguments)` | default simp set / closing |
| 1843 | `rw` | `Cfg.workTapeSymbols_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1844 | `show` | `Function.update e.workTapes 1` | goal restatement (own statement form; no unfolding of other files) |
| 1847 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1847 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1847 | `rw` | `Function.update_of_ne (by omega)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1852 | `rw` | `MultiTapeTM.runFrom_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 1852 | `rw` | `hst` | local hypothesis/term |
| 1855 | `rw` | `h1` | local hypothesis/term |
| 1871 | `rw` | `(no arguments)` | default simp set / closing |
| 1877 | `show` | `Function.update (Function.update e.workTapes 1` | goal restatement (own statement form; no unfolding of other files) |
| 1882 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1882 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1882 | `rw` | `Function.update_idem` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1886 | `rw` | `(no arguments)` | default simp set / closing |
| 1887 | `simp only` | `nf_leaf` | own (this file) |
| 1888 | `rw` | `hsym1` | local hypothesis/term |
| 1888 | `rw` | `if_pos hdec` | core thm (Init.Core) |
| 1897 | `simp only` | `he₁` | local hypothesis/term |
| 1897 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1897 | `simp only` | `SignType.coe_zero` | core/Mathlib lemma (applied definitionally by simp: no constant left in the term) |
| 1897 | `simp only` | `add_zero` | Mathlib thm (Mathlib.Algebra.Group.Defs) |
| 1899 | `simp only` | `he₁` | local hypothesis/term |
| 1899 | `simp only` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1906 | `simp only` | `nf_leaf` | own (this file) |
| 1907 | `rw` | `hsym1` | local hypothesis/term |
| 1907 | `rw` | `if_pos hdec` | core thm (Init.Core) |
| 1909 | `rw` | `htape2` | local hypothesis/term |
| 1919 | `rw` | `(no arguments)` | default simp set / closing |
| 1926 | `rw` | `(no arguments)` | default simp set / closing |
| 1931 | `rw` | `h2` | local hypothesis/term |
| 1934 | `rw` | `h3` | local hypothesis/term |
| 1937 | `rw` | `h4` | local hypothesis/term |
| 1940 | `show` | `moveInputPos (moveInputPos (moveInputPos (moveInputPos e.inputPos 0) 0) 0) 0 = _` | goal restatement (own statement form; no unfolding of other files) |
| 1941 | `rw` | `moveInputPos_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1941 | `rw` | `moveInputPos_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1941 | `rw` | `moveInputPos_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1941 | `rw` | `moveInputPos_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 1946 | `simp only` | `he₂` | local hypothesis/term |
| 1946 | `simp only` | `he₁` | local hypothesis/term |
| 1946 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1947 | `rw` | `hm₂` | local hypothesis/term |
| 1947 | `rw` | `hm₃` | local hypothesis/term |
| 1948 | `simp` | `(no arguments)` | default simp set / closing |
| 1949 | `simp only` | `he₂` | local hypothesis/term |
| 1949 | `simp only` | `he₁` | local hypothesis/term |
| 1949 | `simp only` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 1954 | `rw` | `(no arguments)` | default simp set / closing |
| 1956 | `simp only` | `nf_leaf` | own (this file) |
| 1957 | `rw` | `hsym1, if_neg hdec])` | local hypothesis/term |
| 1993 | `rw` | `(no arguments)` | default simp set / closing |
| 2000 | `simp only` | `nf_leaf` | own (this file) |
| 2001 | `rw` | `if_pos h1, hsym, Option.getD_some, h3, h4, h2, hq])` | core thm (Init.Core) |
| 2009 | `simp only` | `hc` | local hypothesis/term |
| 2009 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2009 | `simp only` | `SignType.coe_one` | Mathlib thm (Mathlib.Data.Sign.Defs) |
| 2012 | `simp only` | `hc` | local hypothesis/term |
| 2012 | `simp only` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2014 | `rw` | `(no arguments)` | default simp set / closing |
| 2016 | `simp only` | `nf_leaf` | own (this file) |
| 2017 | `rw` | `if_pos h1, h2, hn])` | core thm (Init.Core) |
| 2031 | `rw` | `(h.1 y).1` | local hypothesis/term |
| 2031 | `rw` | `(h.1 y).2` | local hypothesis/term |
| 2033 | `rw` | `if_pos hy` | core thm (Init.Core) |
| 2033 | `rw` | `if_pos hy` | core thm (Init.Core) |
| 2034 | `unfold` | `nf_blockDecode` | own (this file) |
| 2038 | `rw` | `if_neg hy` | core thm (Init.Core) |
| 2038 | `rw` | `if_neg hy` | core thm (Init.Core) |
| 2038 | `rw` | `h.2 y hy` | local hypothesis/term |
| 2055 | `rw` | `min_le_iff` | Mathlib thm (Mathlib.Order.MinMax) |
| 2056 | `rw` | `le_max_iff` | Mathlib thm (Mathlib.Order.MinMax) |
| 2062 | `unfold` | `nf_blockWrite` | own (this file) |
| 2064 | `rw` | `hzy` | local hypothesis/term |
| 2066 | `rw` | `Function.update_of_ne e2` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2067 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2067 | `simp only` | `if_pos hy` | core thm (Init.Core) |
| 2067 | `simp only` | `and_self` | core thm (Init.SimpLemmas) |
| 2072 | `rw` | `(no arguments)` | default simp set / closing |
| 2075 | `rw` | `if_pos hz'` | core thm (Init.Core) |
| 2075 | `rw` | `if_pos hz'` | core thm (Init.Core) |
| 2075 | `rw` | `if_pos ((hin z hzy).mpr hz')` | core thm (Init.Core) |
| 2075 | `rw` | `if_pos ((hin z hzy).mpr hz')` | core thm (Init.Core) |
| 2077 | `rw` | `(no arguments)` | default simp set / closing |
| 2081 | `rw` | `Function.update_of_ne hzy` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2094 | `rw` | `(h.1 z).1` | local hypothesis/term |
| 2096 | `rw` | `if_pos hzi` | core thm (Init.Core) |
| 2098 | `rw` | `if_neg hzi` | core thm (Init.Core) |
| 2101 | `rw` | `(h.1 z).2` | local hypothesis/term |
| 2103 | `rw` | `if_pos hzi` | core thm (Init.Core) |
| 2105 | `rw` | `if_neg hzi` | core thm (Init.Core) |
| 2112 | `simp` | `(no arguments)` | default simp set / closing |
| 2180 | `simp only` | `he` | local hypothesis/term |
| 2184 | `rw` | `hew1` | local hypothesis/term |
| 2184 | `rw` | `hep1` | local hypothesis/term |
| 2184 | `rw` | `hpos` | local hypothesis/term |
| 2184 | `rw` | `Cfg.workTapeSymbols_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 2192 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2192 | `rw` | `hrun` | local hypothesis/term |
| 2201 | `simp only` | `nf_vstep` | own (this file) |
| 2201 | `simp only` | `hq` | local hypothesis/term |
| 2202 | `rw` | `Action.apply_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Simulation) |
| 2202 | `rw` | `← hok0` | local hypothesis/term |
| 2204 | `simp only` | `nf_vstep` | own (this file) |
| 2204 | `simp only` | `hq` | local hypothesis/term |
| 2205 | `rw` | `Action.apply_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 2209 | `rw` | `hvt` | local hypothesis/term |
| 2214 | `simpa` | `(no arguments)` | default simp set / closing |
| 2216 | `simp only` | `List.length_singleton` | core/Mathlib lemma (applied definitionally by simp: no constant left in the term) |
| 2219 | `simp` | `(no arguments)` | default simp set / closing |
| 2220 | `simp` | `(no arguments)` | default simp set / closing |
| 2221 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2221 | `rw` | `hrun` | local hypothesis/term |
| 2221 | `rw` | `h2s` | local hypothesis/term |
| 2225 | `show` | `Function.update d.workTapes 1 (nf_blockWrite (e.workTapes 1) (e.workTapePos 1) n) = _` | goal restatement (own statement form; no unfolding of other files) |
| 2226 | `rw` | `hew1` | local hypothesis/term |
| 2226 | `rw` | `hep1` | local hypothesis/term |
| 2226 | `rw` | `hpos` | local hypothesis/term |
| 2230 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2231 | `rw` | `hep1` | local hypothesis/term |
| 2231 | `rw` | `hpos` | local hypothesis/term |
| 2232 | `simp only` | `he` | local hypothesis/term |
| 2232 | `simp only` | `Function.update_of_ne hi` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2232 | `simp only` | `List.length_singleton` | core/Mathlib lemma (applied definitionally by simp: no constant left in the term) |
| 2232 | `simp only` | `Nat.mul_one` | core thm (Init.Data.Nat.Basic) |
| 2235 | `simpa` | `(no arguments)` | default simp set / closing |
| 2246 | `show` | `nf_blocks (Function.update e.workTapes 1` | goal restatement (own statement form; no unfolding of other files) |
| 2248 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2248 | `rw` | `hew1` | local hypothesis/term |
| 2248 | `rw` | `hep1` | local hypothesis/term |
| 2248 | `rw` | `hpos` | local hypothesis/term |
| 2251 | `show` | `Function.update e.workTapePos 1 (e.workTapePos 1 + 2 * ((a.workTapes t).2 : ℤ)) 1 = _` | goal restatement (own statement form; no unfolding of other files) |
| 2252 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2252 | `rw` | `hep1` | local hypothesis/term |
| 2252 | `rw` | `hpos` | local hypothesis/term |
| 2252 | `rw` | `hvp` | local hypothesis/term |
| 2258 | `simp only` | `hd'` | local hypothesis/term |
| 2258 | `simp only` | `he` | local hypothesis/term |
| 2261 | `simp only` | `hd'` | local hypothesis/term |
| 2261 | `simp only` | `he` | local hypothesis/term |
| 2262 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2262 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2263 | `rw` | `hw0` | local hypothesis/term |
| 2263 | `rw` | `hp0` | local hypothesis/term |
| 2267 | `simp` | `(no arguments)` | default simp set / closing |
| 2270 | `rw` | `hvp` | local hypothesis/term |
| 2271 | `rw` | `hvp` | local hypothesis/term |
| 2273 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2273 | `rw` | `hrun` | local hypothesis/term |
| 2273 | `rw` | `h4s` | local hypothesis/term |
| 2279 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2279 | `rw` | `hrun` | local hypothesis/term |
| 2283 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2283 | `rw` | `hrun4` | local hypothesis/term |
| 2286 | `simp only` | `List.length_cons` | core thm (Init.Data.List.Basic) |
| 2286 | `rw` | `Nat.mul_add` | core thm (Init.Data.Nat.Basic) |
| 2286 | `rw` | `← hT` | local hypothesis/term |
| 2288 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2288 | `rw` | `hrun4` | local hypothesis/term |
| 2288 | `rw` | `hcfg` | local hypothesis/term |
| 2292 | `show` | `Function.update (Function.update d.workTapes 1 _) 1 B = _` | goal restatement (own statement form; no unfolding of other files) |
| 2293 | `rw` | `Function.update_idem` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2297 | `simp only` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2300 | `simp only` | `(no arguments)` | default simp set / closing |
| 2301 | `show` | `(0 : Fin 2) ≠ 1 by decide), List.length_cons]` | goal restatement (own statement form; no unfolding of other files) |
| 2305 | `simp only` | `List.length_cons` | core thm (Init.Data.List.Basic) |
| 2308 | `rw` | `min_le_iff` | Mathlib thm (Mathlib.Order.MinMax) |
| 2309 | `rw` | `le_max_iff` | Mathlib thm (Mathlib.Order.MinMax) |
| 2317 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2317 | `rw` | `hrun4` | local hypothesis/term |
| 2321 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2321 | `rw` | `hrun` | local hypothesis/term |
| 2339 | `rw` | `hL` | local hypothesis/term |
| 2341 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2341 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2343 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2345 | `rw` | `hs` | local hypothesis/term |
| 2348 | `rw` | `FinTM.bufferTape_left` | TCSlib thm (TCSlib.Complexity.TuringMachine.Simulation) |
| 2353 | `rw` | `hpL` | local hypothesis/term |
| 2353 | `rw` | `FinTM.bufferTape_nat` | TCSlib thm (TCSlib.Complexity.TuringMachine.Simulation) |
| 2353 | `rw` | `List.getElem?_eq_none (by rw [List.length_ofFn])` | core thm (Init.GetElem) |
| 2359 | `rw` | `FinTM.bufferTape_nat` | TCSlib thm (TCSlib.Complexity.TuringMachine.Simulation) |
| 2359 | `rw` | `List.getElem?_ofFn` | core thm (Init.Data.List.OfFn) |
| 2360 | `simp only` | `hm` | local hypothesis/term |
| 2360 | `simp only` | `dite_true` | local hypothesis/term |
| 2363 | `rw` | `hb` | local hypothesis/term |
| 2365 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2367 | `rw` | `if_pos hq` | core thm (Init.Core) |
| 2368 | `rw` | `if_neg hq` | core thm (Init.Core) |
| 2381 | `rw` | `List.flatMap_cons` | core thm (Init.Data.List.Basic) |
| 2381 | `rw` | `List.length_append` | core thm (Init.Data.List.Basic) |
| 2381 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2381 | `rw` | `ih` | local hypothesis/term |
| 2381 | `rw` | `List.length_cons` | core thm (Init.Data.List.Basic) |
| 2437 | `unfold` | `nf_tapeEntry` | own (this file) |
| 2438 | `rw` | `dif_neg hk` | core thm (Init.Core) |
| 2440 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 2440 | `rw` | `he` | local hypothesis/term |
| 2442 | `rw` | `hq` | local hypothesis/term |
| 2444 | `rw` | `MultiTapeTM.runFrom_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2446 | `rw` | `MultiTapeTM.runFrom_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2447 | `rw` | `MultiTapeTM.runFrom_zero` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2447 | `rw` | `Cfg.mapState_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 2447 | `rw` | `hout` | local hypothesis/term |
| 2455 | `unfold` | `nf_tapeEntry` | own (this file) |
| 2456 | `rw` | `dif_pos hk` | core thm (Init.Core) |
| 2464 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 2464 | `rw` | `Cfg.init_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 2467 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 2467 | `rw` | `Cfg.init_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 2469 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 2469 | `rw` | `Cfg.init_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 2472 | `show` | `nf_blocks (c.workTapes 1) _ _ _ _` | goal restatement (own statement form; no unfolding of other files) |
| 2473 | `rw` | `hB` | local hypothesis/term |
| 2473 | `rw` | `hinit_tape` | local hypothesis/term |
| 2475 | `rw` | `if_neg (by omega)` | core thm (Init.Core) |
| 2475 | `rw` | `if_neg (by omega)` | core thm (Init.Core) |
| 2479 | `show` | `c.workTapePos 1 = _` | goal restatement (own statement form; no unfolding of other files) |
| 2479 | `rw` | `hinit_pos` | local hypothesis/term |
| 2479 | `rw` | `hinit_pos` | local hypothesis/term |
| 2480 | `rw` | `hinit_pos` | local hypothesis/term |
| 2482 | `show` | `c.workTapes 0 (c.workTapePos 0 + p) = _` | goal restatement (own statement form; no unfolding of other files) |
| 2483 | `rw` | `hA` | local hypothesis/term |
| 2483 | `rw` | `hA0` | local hypothesis/term |
| 2483 | `rw` | `zero_add` | Mathlib thm (Mathlib.Algebra.Group.Defs) |
| 2483 | `rw` | `FinTM.bufferTape_nat` | TCSlib thm (TCSlib.Complexity.TuringMachine.Simulation) |
| 2488 | `show` | `(match nf_leafExit N q with` | goal restatement (own statement form; no unfolding of other files) |
| 2490 | `rw` | `h` | local hypothesis/term |
| 2494 | `rw` | `he` | local hypothesis/term |
| 2494 | `rw` | `hre` | local hypothesis/term |
| 2495 | `unfold` | `nf_V` | own (this file) |
| 2496 | `rw` | `(no arguments)` | default simp set / closing |
| 2514 | `rw` | `hc₁` | local hypothesis/term |
| 2519 | `simp only` | `hc₁'` | local hypothesis/term |
| 2519 | `simp only` | `hc₁` | local hypothesis/term |
| 2519 | `simp only` | `hdL` | local hypothesis/term |
| 2520 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2520 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2520 | `rw` | `hA0` | local hypothesis/term |
| 2520 | `rw` | `zero_add` | Mathlib thm (Mathlib.Algebra.Group.Defs) |
| 2520 | `rw` | `hslen` | local hypothesis/term |
| 2523 | `simp only` | `hc₁'` | local hypothesis/term |
| 2523 | `simp only` | `hc₁` | local hypothesis/term |
| 2523 | `simp only` | `hdL` | local hypothesis/term |
| 2524 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2524 | `rw` | `hA` | local hypothesis/term |
| 2538 | `simp only` | `hc₃'` | local hypothesis/term |
| 2539 | `rw` | `h3w` | local hypothesis/term |
| 2540 | `simp only` | `hc₁'` | local hypothesis/term |
| 2540 | `simp only` | `hc₁` | local hypothesis/term |
| 2541 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2543 | `simp only` | `hc₃'` | local hypothesis/term |
| 2544 | `rw` | `h3p1` | local hypothesis/term |
| 2545 | `simp only` | `hc₁'` | local hypothesis/term |
| 2545 | `simp only` | `hc₁` | local hypothesis/term |
| 2546 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2553 | `rw` | `hB3` | local hypothesis/term |
| 2553 | `rw` | `hP3` | local hypothesis/term |
| 2561 | `rw` | `h5w0` | local hypothesis/term |
| 2562 | `simp only` | `hc₃'` | local hypothesis/term |
| 2563 | `rw` | `h3w` | local hypothesis/term |
| 2564 | `simp only` | `hc₁'` | local hypothesis/term |
| 2564 | `simp only` | `hc₁` | local hypothesis/term |
| 2564 | `simp only` | `hdL` | local hypothesis/term |
| 2565 | `rw` | `Function.update_of_ne (by decide)` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2565 | `rw` | `hA` | local hypothesis/term |
| 2567 | `rw` | `h5p0` | local hypothesis/term |
| 2568 | `simp only` | `hc₃'` | local hypothesis/term |
| 2572 | `rw` | `h5w1 q` | local hypothesis/term |
| 2572 | `rw` | `hB3` | local hypothesis/term |
| 2572 | `rw` | `hP3` | local hypothesis/term |
| 2575 | `rw` | `h5o` | local hypothesis/term |
| 2576 | `simp only` | `hc₃'` | local hypothesis/term |
| 2577 | `rw` | `h3o` | local hypothesis/term |
| 2578 | `simp only` | `hc₁'` | local hypothesis/term |
| 2578 | `simp only` | `hc₁` | local hypothesis/term |
| 2578 | `simp only` | `hdL` | local hypothesis/term |
| 2588 | `rw` | `he` | local hypothesis/term |
| 2588 | `rw` | `hre` | local hypothesis/term |
| 2589 | `unfold` | `nf_V` | own (this file) |
| 2590 | `rw` | `hR` | local hypothesis/term |
| 2590 | `rw` | `hre1` | local hypothesis/term |
| 2595 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2595 | `rw` | `hrun1` | local hypothesis/term |
| 2595 | `rw` | `h3'` | local hypothesis/term |
| 2595 | `rw` | `hre3` | local hypothesis/term |
| 2599 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2599 | `rw` | `hrun2` | local hypothesis/term |
| 2599 | `rw` | `h5'` | local hypothesis/term |
| 2613 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2613 | `rw` | `hrun3` | local hypothesis/term |
| 2618 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2618 | `rw` | `hrun1` | local hypothesis/term |
| 2622 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2622 | `rw` | `h3'` | local hypothesis/term |
| 2622 | `rw` | `hre3` | local hypothesis/term |
| 2626 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2626 | `rw` | `h5'` | local hypothesis/term |
| 2628 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2628 | `rw` | `hrun3` | local hypothesis/term |
| 2628 | `rw` | `hacc2` | local hypothesis/term |
| 2631 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2631 | `rw` | `hrun3` | local hypothesis/term |
| 2638 | `rw` | `e3` | local hypothesis/term |
| 2639 | `rw` | `e1` | local hypothesis/term |
| 2640 | `rw` | `e2` | local hypothesis/term |
| 2650 | `rw` | `he` | local hypothesis/term |
| 2650 | `rw` | `hre` | local hypothesis/term |
| 2651 | `unfold` | `nf_V` | own (this file) |
| 2652 | `rw` | `hR` | local hypothesis/term |
| 2652 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 2652 | `rw` | `hrj` | local hypothesis/term |
| 2656 | `rw` | `hver` | local hypothesis/term |
| 2657 | `simp` | `(no arguments)` | default simp set / closing |
| 2711 | `rw` | `nf_tag` | own (this file) |
| 2731 | `rw` | `hV` | local hypothesis/term |
| 2732 | `unfold` | `nf_V` | own (this file) |
| 2733 | `rw` | `hp0 u hu` | local hypothesis/term |
| 2741 | `rw` | `hV` | local hypothesis/term |
| 2742 | `unfold` | `nf_V` | own (this file) |
| 2743 | `rw` | `hD` | local hypothesis/term |
| 2743 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 2743 | `rw` | `streamStartCfg_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 2744 | `simp only` | `Option.map_some` | core/Mathlib lemma (applied definitionally by simp: no constant left in the term) |
| 2745 | `rw` | `if_neg hpass` | core thm (Init.Core) |
| 2748 | `rw` | `hver` | local hypothesis/term |
| 2749 | `simp` | `(no arguments)` | default simp set / closing |
| 2755 | `rw` | `hdS` | local hypothesis/term |
| 2755 | `rw` | `streamStartCfg_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 2760 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 2760 | `rw` | `Cfg.init_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 2764 | `show` | `dS.inputPos = _` | goal restatement (own statement form; no unfolding of other files) |
| 2765 | `rw` | `hdS` | local hypothesis/term |
| 2765 | `rw` | `streamStartCfg_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 2765 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 2765 | `rw` | `Cfg.init_inputPos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 2768 | `show` | `dS.workTapes 0 (dS.workTapePos 0 + p) = _` | goal restatement (own statement form; no unfolding of other files) |
| 2769 | `rw` | `(no arguments)` | default simp set / closing |
| 2775 | `show` | `(match nf_leafExit N q with` | goal restatement (own statement form; no unfolding of other files) |
| 2777 | `rw` | `h` | local hypothesis/term |
| 2782 | `rw` | `hV` | local hypothesis/term |
| 2783 | `unfold` | `nf_V` | own (this file) |
| 2784 | `rw` | `hD` | local hypothesis/term |
| 2785 | `simp only` | `hpass` | local hypothesis/term |
| 2785 | `simp only` | `if_true` | core thm (Init.ByCases) |
| 2790 | `rw` | `hV` | local hypothesis/term |
| 2791 | `unfold` | `nf_V` | own (this file) |
| 2792 | `rw` | `(no arguments)` | default simp set / closing |
| 2802 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2802 | `rw` | `hrun0` | local hypothesis/term |
| 2816 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2816 | `rw` | `hrun0` | local hypothesis/term |
| 2816 | `rw` | `hV` | local hypothesis/term |
| 2817 | `unfold` | `nf_V` | own (this file) |
| 2818 | `rw` | `hR` | local hypothesis/term |
| 2818 | `rw` | `Cfg.mapState_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.StateRenaming) |
| 2818 | `rw` | `hrj` | local hypothesis/term |
| 2823 | `rw` | `hver` | local hypothesis/term |
| 2824 | `simp` | `(no arguments)` | default simp set / closing |
| 2837 | `rw` | `hc₁` | local hypothesis/term |
| 2842 | `simp only` | `hc₁'` | local hypothesis/term |
| 2842 | `simp only` | `hc₁` | local hypothesis/term |
| 2842 | `simp only` | `hdL` | local hypothesis/term |
| 2842 | `simp only` | `hdS` | local hypothesis/term |
| 2843 | `rw` | `Function.update_self` | Mathlib thm (Mathlib.Logic.Function.Basic) |
| 2843 | `rw` | `streamStartCfg_workTapePos` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 2843 | `rw` | `zero_add` | Mathlib thm (Mathlib.Algebra.Group.Defs) |
| 2843 | `rw` | `hslen` | local hypothesis/term |
| 2846 | `simp only` | `hc₁'` | local hypothesis/term |
| 2846 | `simp only` | `hc₁` | local hypothesis/term |
| 2846 | `simp only` | `hdL` | local hypothesis/term |
| 2846 | `simp only` | `hdS` | local hypothesis/term |
| 2847 | `rw` | `streamStartCfg_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 2847 | `rw` | `if_pos rfl` | core thm (Init.Core) |
| 2855 | `rw` | `h3w` | local hypothesis/term |
| 2859 | `rw` | `h3w` | local hypothesis/term |
| 2861 | `simp only` | `hc₁'` | local hypothesis/term |
| 2861 | `simp only` | `hc₁` | local hypothesis/term |
| 2861 | `simp only` | `hdL` | local hypothesis/term |
| 2861 | `simp only` | `hdS` | local hypothesis/term |
| 2862 | `rw` | `streamStartCfg_workTapes` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 2862 | `rw` | `if_neg (by decide)` | core thm (Init.Core) |
| 2864 | `rw` | `h3o` | local hypothesis/term |
| 2865 | `simp only` | `hc₁'` | local hypothesis/term |
| 2865 | `simp only` | `hc₁` | local hypothesis/term |
| 2865 | `simp only` | `hdL` | local hypothesis/term |
| 2865 | `simp only` | `hdS` | local hypothesis/term |
| 2866 | `rw` | `streamStartCfg_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.NDHost) |
| 2874 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2874 | `rw` | `hrun0` | local hypothesis/term |
| 2874 | `rw` | `hV` | local hypothesis/term |
| 2875 | `unfold` | `nf_V` | own (this file) |
| 2876 | `rw` | `hR` | local hypothesis/term |
| 2876 | `rw` | `hre1` | local hypothesis/term |
| 2881 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2881 | `rw` | `hrun1` | local hypothesis/term |
| 2881 | `rw` | `h3'` | local hypothesis/term |
| 2884 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2884 | `rw` | `hrun2` | local hypothesis/term |
| 2890 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2890 | `rw` | `hrun1` | local hypothesis/term |
| 2894 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2894 | `rw` | `h3'` | local hypothesis/term |
| 2896 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2896 | `rw` | `hrun2` | local hypothesis/term |
| 2896 | `rw` | `hacc2` | local hypothesis/term |
| 2896 | `rw` | `nf_allPass_iff` | own (this file) |
| 2899 | `rw` | `MultiTapeTM.runFrom_add` | TCSlib thm (TCSlib.Complexity.TuringMachine.Deterministic) |
| 2899 | `rw` | `hrun2` | local hypothesis/term |
| 2900 | `rw` | `hT₁` | local hypothesis/term |
| 2902 | `rw` | `e2` | local hypothesis/term |
| 2920 | `rw` | `hlen` | local hypothesis/term |
| 2923 | `rw` | `Nat.mul_add` | core thm (Init.Data.Nat.Basic) |
| 2923 | `rw` | `Nat.mul_one` | core thm (Init.Data.Nat.Basic) |
| 2929 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2929 | `rw` | `List.length_nil` | core thm (Init.Data.List.Basic) |
| 2932 | `rw` | `hlen` | local hypothesis/term |
| 2933 | `rw` | `hlen` | local hypothesis/term |
| 2935 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2935 | `rw` | `hlen` | local hypothesis/term |
| 2937 | `rw` | `List.getElem_ofFn` | core thm (Init.Data.List.OfFn) |
| 2938 | `rw` | `List.flatMap_def` | core thm (Init.Data.List.Lemmas) |
| 2938 | `rw` | `List.map_ofFn` | Mathlib thm (Mathlib.Data.List.OfFn) |
| 2941 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 2942 | `rw` | `List.getElem_ofFn` | core thm (Init.Data.List.OfFn) |
| 2945 | `rw` | `Nat.mul_add` | core thm (Init.Data.Nat.Basic) |
| 2945 | `rw` | `Nat.mul_one` | core thm (Init.Data.Nat.Basic) |
| 2947 | `rw` | `e` | local hypothesis/term |
| 2947 | `rw` | `List.getElem?_eq_getElem (hidx ⟨r, hr⟩ ⟨2 * k + 3, by omega⟩)` | core thm (Init.GetElem) |
| 2979 | `rw` | `nf_entry` | own (this file) |
| 2997 | `rw` | `List.take_zero` | core thm (Init.Data.List.Basic) |
| 2997 | `rw` | `List.foldl_nil` | core thm (Init.Data.List.Basic) |
| 2997 | `rw` | `List.take_zero` | core thm (Init.Data.List.Basic) |
| 2997 | `rw` | `NDTM.runWith_nil` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 3005 | `rwa` | `ih` | local hypothesis/term |
| 3006 | `rw` | `(no arguments)` | default simp set / closing |
| 3007 | `rw` | `List.length_map` | core thm (Init.Data.List.Lemmas) |
| 3017 | `simp only` | `nf_vstep` | own (this file) |
| 3017 | `simp only` | `hq` | local hypothesis/term |
| 3018 | `rw` | `NDTM.stepWith_of_some hq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 3019 | `unfold` | `nf_act` | own (this file) |
| 3020 | `rw` | `Option.getD_some` | core thm (Init.Data.Option.Basic) |
| 3020 | `rw` | `hd0` | local hypothesis/term |
| 3020 | `rw` | `hds` | local hypothesis/term |
| 3020 | `rw` | `List.getElem_map` | core thm (Init.Data.List.Lemmas) |
| 3052 | `rw` | `hrs` | local hypothesis/term |
| 3054 | `rw` | `hrs` | local hypothesis/term |
| 3054 | `rw` | `List.length_ofFn` | core thm (Init.Data.List.OfFn) |
| 3056 | `rw` | `hrlen` | local hypothesis/term |
| 3062 | `rw` | `List.getElem_ofFn` | core thm (Init.Data.List.OfFn) |
| 3066 | `rw` | `hrlen` | local hypothesis/term |
| 3066 | `rw` | `List.length_nil` | core thm (Init.Data.List.Basic) |
| 3071 | `rw` | `hget r hr` | local hypothesis/term |
| 3074 | `rw` | `List.length_map` | core thm (Init.Data.List.Lemmas) |
| 3074 | `rw` | `hrlen` | local hypothesis/term |
| 3076 | `rw` | `List.getElem_map` | core thm (Init.Data.List.Lemmas) |
| 3076 | `rw` | `hget r (by rw [List.length_map] at h1; exact h1)` | local hypothesis/term |
| 3084 | `rw` | `nf_vrun_of_ok N x rs r hr.le (fun r' h' i' => ih r' h' (by omega) i')` | own (this file) |
| 3084 | `rw` | `hmap` | local hypothesis/term |
| 3085 | `rw` | `← hrlen` | local hypothesis/term |
| 3086 | `rw` | `hget r hr` | local hypothesis/term |
| 3090 | `rw` | `← hdisp` | local hypothesis/term |
| 3092 | `rw` | `hdisp` | local hypothesis/term |
| 3096 | `rw` | `hrlen` | local hypothesis/term |
| 3128 | `rw` | `hs` | local hypothesis/term |
| 3128 | `rw` | `hA` | local hypothesis/term |
| 3133 | `unfold` | `nf_C` | own (this file) |
| 3134 | `rw` | `hA` | local hypothesis/term |
| 3154 | `rw` | `← hw` | local hypothesis/term |
| 3154 | `rw` | `List.take_length` | core thm (Init.Data.List.TakeDrop) |
| 3160 | `rw` | `← hw` | local hypothesis/term |
| 3160 | `rw` | `List.take_length` | core thm (Init.Data.List.TakeDrop) |
| 3165 | `rw` | `h00` | local hypothesis/term |
| 3165 | `rw` | `List.take_zero` | core thm (Init.Data.List.Basic) |
| 3165 | `rw` | `NDTM.runWith_nil` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 3165 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 3165 | `rw` | `Cfg.init_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 3168 | `rw` | `hw₀` | local hypothesis/term |
| 3168 | `rw` | `List.length_take` | core thm (Init.Data.List.Nat.TakeDrop) |
| 3172 | `rw` | `hw₀len` | local hypothesis/term |
| 3172 | `rw` | `List.length_nil` | core thm (Init.Data.List.Basic) |
| 3176 | `rw` | `hw₀len` | local hypothesis/term |
| 3177 | `rw` | `hw₀` | local hypothesis/term |
| 3177 | `rw` | `List.take_take` | core thm (Init.Data.List.Nat.TakeDrop) |
| 3177 | `rw` | `Nat.min_eq_left hr.le` | core thm (Init.Data.Nat.MinMax) |
| 3181 | `rw` | `hw₀` | local hypothesis/term |
| 3181 | `rw` | `List.take_append_drop` | core thm (Init.Data.List.TakeDrop) |
| 3181 | `rw` | `NDTM.runWith_of_halt _ hspec` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 3182 | `rw` | `hw₀` | local hypothesis/term |
| 3182 | `rw` | `← hsplit` | local hypothesis/term |
| 3189 | `rw` | `nf_display_length` | own (this file) |
| 3189 | `rw` | `hw₀len` | local hypothesis/term |
| 3190 | `rw` | `hw₀len` | local hypothesis/term |
| 3192 | `rw` | `← nf_entry nf_P x (nf_display N x w₀)` | own (this file) |
| 3218 | `rw` | `List.take_length` | core thm (Init.Data.List.TakeDrop) |
| 3218 | `rw` | `← hwlen` | local hypothesis/term |
| 3218 | `rw` | `List.take_length` | core thm (Init.Data.List.TakeDrop) |
| 3221 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 3221 | `rw` | `Cfg.init_state` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 3223 | `rw` | `NDTM.initCfg_eq` | TCSlib thm (TCSlib.Complexity.TuringMachine.Nondeterministic) |
| 3223 | `rw` | `Cfg.init_output` | TCSlib thm (TCSlib.Complexity.TuringMachine.Configuration) |
| 3223 | `rw` | `StepBlock.outputSummary_nil` | TCSlib thm (TCSlib.Complexity.TuringMachine.Build.StepBlock) |
| 3226 | `rw` | `hfin` | local hypothesis/term |
| 3231 | `rw` | `hsw` | local hypothesis/term |
| 3235 | `unfold` | `nf_sweepPass` | own (this file) |
| 3236 | `rw` | `Bool.and_eq_true` | core thm (Init.SimpLemmas) |
| 3236 | `rw` | `Bool.and_eq_true` | core thm (Init.SimpLemmas) |
| 3236 | `rw` | `Bool.and_eq_true` | core thm (Init.SimpLemmas) |
| 3238 | `rw` | `hc1` | local hypothesis/term |
| 3258 | `rw` | `nf_entry` | own (this file) |
