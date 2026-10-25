# G4 continuation 4: per-pair dispositions for the 173 pairs justified by class (zips 1–3)

Gate 75, minor 6 (2026-10-25). The worker's cumulative pair list
(`screens/screen-pairs-since-base-cp7.md` in `fill-s13d-g4-cont4.zip`) gives 327 of the 500 new
in-file pairs a line of their own. The other 173, first seen in zips 1–3, it justifies by class in
those zips' reports: "the contract layer's field scaffolding: the `Cfg.ext` branches, the
`seq_time`/`seq_lo` openings, the `zoneRowPre` readings". Those reports and the checkpoint zips were
not delivered, so this file gives each of the 173 its own disposition, by the maintainer.

**Method** (`classify.py.txt`, run on the landing head's `Build/ZoneRebalance.lean`). The screen's
own extraction and greedy tiling (`scripts/copy-text-screen-v3.py`, its helper definitions imported
unchanged, the screen's argument order) recompute each pair's shared tiles. Every pair reproduces
the worker's figures exactly (shared characters and source length). Each pair is then given the
classes whose markers occur in its shared tiles, and the two declarations' headers are compared.

**Results.** 173 pairs, all inside `Build/ZoneRebalance`, from 50% to 84%. **No pair has two
declarations with the same statement.** Thirteen pairs are between two `def`s whose types are
inferred: they share only the binders `{k : ℕ} (x : List (ZoneSym k))` and are different contracts
or rows, with bodies that compose different machines. Every pair falls in at least one class:

- **contract-opening** (146 pairs): the contract layer's openings:
  `Contract.seq_*`/`Contract.ofSegment_*` and catalog `_contract_*` field rewrites,
  `zr_reindexContract` re-indexing.
- **field-branches** (142 pairs): the `Cfg.ext` branches over an endpoint: `Cfg.mapState_*`,
  `seekPost_*`, `funext`, `Function.update` rewrites.
- **zoneRowPre-reading** (39 pairs): readings of the zone layout and the scratch ruler:
  `zoneRowPre`, `zonedTape`, `zr_scratchAt`.
- **instance-plumbing** (4 pairs): the per-phase `DecidableEq`/`Fintype` instances and their
  `synthInstance.maxSize` options.
- **phase-literals** (4 pairs): the rows' shared exit-state literals
  (`Sum.inr (Sum.inr … SweepPhase.done)`).
- **arithmetic-ledger** (15 pairs): the time ledgers' arithmetic openings (`zr_extent_cost`,
  `zoneStart_mono`, `zoneStart_eq`, `omega`).
- **word-reading** (6 pairs): the ruler and word readings (`List.length_*`, `zr_rulerTape_word`,
  `FinTM.bufferTape`).

**Disposition (each row).** Scaffolding shared by sibling declarations of one contract layer, with
different statements: not a copy, nothing to factor (the shared text is rewrite lists and case
splits over different contracts). No row is a ledger member. The census is unchanged: RI-1 is the
file's one recorded family.

| # | Share | Target ⟵ source | Zip | Classes | Statements | Longest shared tile (chars: start) |
|---|---|---|---|---|---|---|
| 1 | 84% (71/85) | `zr_rightLeftRow` ⟵ `zr_rightPassRow` | 3 | phase-literals | same binders; types inferred | 42: `(Sum.inr(Sum.inr(Sum.inrSweepPhase.done)))` |
| 2 | 81% (372/461) | `zr_adjustedBack_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 141: `_state,Option.map_some]·simponly[Cfg.mapState_inputPos,seekP` |
| 3 | 81% (374/461) | `zr_leftMove_fields` ⟵ `zr_return_post` | 2 | contract-opening, field-branches | differ | 229: `Contract,Contract.ofSegment_post,skipTM_contract_post]applyC` |
| 4 | 81% (147/181) | `zr_rightLeft_pre` ⟵ `zr_extend_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 5 | 79% (147/186) | `zr_extend_pre` ⟵ `zr_rightLeft_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 6 | 79% (110/140) | `zr_extend_pre` ⟵ `zr_rightPass_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 7 | 79% (133/168) | `zr_leftMove_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches, zoneRowPre-reading | differ | 102: `Contract,Contract.ofSegment_pre]simponly[zr_scratchAt,Cfg.ma` |
| 8 | 79% (110/140) | `zr_rightLeft_pre` ⟵ `zr_rightPass_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 9 | 79% (61/77) | `zr_rightPass_time` ⟵ `zr_body_time` | 1 | contract-opening | differ | 31: `t_time,skipBackTM_contract_time` |
| 10 | 79% (110/140) | `zr_rightReturn_pre` ⟵ `zr_rightPass_pre` | 1 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 11 | 79% (362/461) | `zr_rightRuler_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 73: `Post_inputPos]·funextjqsimponly[Cfg.mapState_workTapes,seekP` |
| 12 | 78% (115/148) | `zr_return_bounds` ⟵ `zr_return_time` | 1 | contract-opening | differ | 43: `e,zr_returnSkipContract,Contract.ofSegment_` |
| 13 | 77% (114/148) | `zr_return_post` ⟵ `zr_return_time` | 1 | contract-opening | differ | 42: `,zr_returnSkipContract,Contract.ofSegment_` |
| 14 | 77% (355/461) | `zr_rightSeekBack_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 212: `_state,Option.map_some]·simponly[Cfg.mapState_inputPos,seekP` |
| 15 | 76% (141/186) | `zr_rightLeft_post` ⟵ `zr_rightLeft_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 16 | 75% (346/461) | `zr_leftPass_fields` ⟵ `zr_return_post` | 2 | contract-opening, field-branches | differ | 115: `applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some]·si` |
| 17 | 75% (76/101) | `zr_test_post` ⟵ `zr_test_time` | 1 | contract-opening | differ | 40: `bysimponly[zr_testContract,Contract.seq_` |
| 18 | 75% (139/186) | `zr_twoSteps_fields` ⟵ `zr_singleton_fields` | 2 | contract-opening | differ | 46: `t,Contract.ofSegment_lo,Contract.ofSegment_hi,` |
| 19 | 74% (125/168) | `zr_leftWrite_fields` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 20 | 73% (70/96) | `zr_extend_time_le` ⟵ `zr_rightPass_time_le` | 3 | arithmetic-ledger | differ | 70: `byhaveh:=zr_extent_costD.1havehm:=zoneStart_mono(Nat.le_add_` |
| 21 | 72% (400/554) | `zr_leftPass_fields` ⟵ `zr_body_post` | 2 | field-branches, arithmetic-ledger | differ | 109: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos,seekPost_wor` |
| 22 | 72% (73/101) | `zr_leftWrite_fields` ⟵ `zr_test_time` | 2 | contract-opening | differ | 73: `Contract.seq_time,zr_stepContract,Contract.ofSegment_time,zr` |
| 23 | 72% (121/168) | `zr_rightLeft_link` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches, zoneRowPre-reading | differ | 61: `zr_scratchAt,Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 24 | 71% (328/461) | `zr_body_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 197: `e]·simponly[Cfg.mapState_inputPos,seekPost_inputPos]·funextj` |
| 25 | 70% (322/461) | `zr_final_fields` ⟵ `zr_return_post` | 3 | contract-opening, field-branches | differ | 62: `Cfg.mapState_workTapePos,seekPost_workTapePos,Function.updat` |
| 26 | 69% (380/554) | `zr_leftMove_fields` ⟵ `zr_body_post` | 2 | field-branches | differ | 120: `e]·simponly[Cfg.mapState_inputPos,seekPost_inputPos]·funextj` |
| 27 | 68% (384/563) | `zr_leftPass_fields` ⟵ `zr_return_bounds` | 2 | contract-opening, field-branches | differ | 167: `TM_contract_post,Cfg.mapState_workTapePos,seekPost_workTapeP` |
| 28 | 68% (140/206) | `zr_rightLeft_link` ⟵ `zr_leftMove_pre` | 2 | contract-opening, field-branches, zoneRowPre-reading | differ | 61: `zr_scratchAt,Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 29 | 67% (295/438) | `zr_finalContract` ⟵ `zr_leftPassContract` | 3 | contract-opening, field-branches, zoneRowPre-reading | same binders; types inferred | 74: `.2(funr=>?_)?_<;>simponly[Cfg.mapState_workTapes,Cfg.mapStat` |
| 30 | 67% (187/280) | `zr_loop_zone_test` ⟵ `zr_loop_zone_word` | 1 | field-branches, arithmetic-ledger | differ | 73: `havehs:=zoneStart_succi.valhavehm:=zoneStart_mono(showi.val+` |
| 31 | 67% (88/131) | `zr_rightLeftRow` ⟵ `zr_rightReturnRow` | 3 | contract-opening, instance-plumbing, phase-literals | same binders; types inferred | 33: `))set_optionsynthInstance.maxSize` |
| 32 | 66% (333/508) | `zr_adjustedBack_post` ⟵ `zr_adjustedBack_copy_pre` | 2 | contract-opening, field-branches | differ | 127: `zr_adjustedWalkContract,Contract.ofSegment_pre,Contract.seq_` |
| 33 | 66% (120/181) | `zr_extendContract` ⟵ `zr_rightLeftContract` | 3 | contract-opening | same binders; types inferred | 120: `Contractx)(funD=>D)funDd_hp=>byrw[(zr_singleton_fields___Dd)` |
| 34 | 66% (67/101) | `zr_return_time` ⟵ `zr_test_time` | 1 | contract-opening | differ | 37: `pContract,Contract.ofSegment_time,zr_` |
| 35 | 66% (120/181) | `zr_rightLeftContract` ⟵ `zr_extendContract` | 3 | contract-opening | same binders; types inferred | 120: `Contractx)(funD=>D)funDd_hp=>byrw[(zr_singleton_fields___Dd)` |
| 36 | 65% (72/110) | `zr_decEqLoopPh` ⟵ `zr_fintypeLoopPh` | 3 | instance-plumbing | differ | 36: `(OptionBool))\|true=>inferInstanceAs(` |
| 37 | 65% (96/148) | `zr_leftWalk_fields` ⟵ `zr_return_time` | 2 | contract-opening | differ | 36: `Contract,Contract.ofSegment_time,zr_` |
| 38 | 65% (380/585) | `zr_leftWrite_fields` ⟵ `zr_test_post` | 2 | contract-opening, field-branches | differ | 85: `Contract.seq_post,zr_stepContract,Contract.ofSegment_post,zr` |
| 39 | 65% (133/206) | `zr_leftWrite_pre` ⟵ `zr_leftMove_pre` | 2 | contract-opening, field-branches, zoneRowPre-reading | differ | 102: `Contract,Contract.ofSegment_pre]simponly[zr_scratchAt,Cfg.ma` |
| 40 | 65% (319/494) | `zr_rightPass_bounds` ⟵ `zr_body_bounds` | 1 | contract-opening, field-branches | differ | 60: `t,zr_cellPost,Cfg.mapState_workTapePos,seekPost_workTapePos,` |
| 41 | 65% (66/101) | `zr_rightPass_time` ⟵ `zr_test_time` | 1 | contract-opening | differ | 36: `Contract,Contract.ofSegment_time,zr_` |
| 42 | 65% (109/168) | `zr_rightReturn_link` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 48: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 43 | 65% (66/101) | `zr_rightReturn_time` ⟵ `zr_test_time` | 1 | contract-opening | differ | 36: `Contract,Contract.ofSegment_time,zr_` |
| 44 | 65% (358/554) | `zr_rightSeekBack_post` ⟵ `zr_body_post` | 1 | contract-opening, field-branches | differ | 191: `e]·simponly[Cfg.mapState_inputPos,seekPost_inputPos]·funextj` |
| 45 | 65% (109/168) | `zr_rightSeekBack_ruler_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 49: `,Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 46 | 64% (108/168) | `zr_final_fields` ⟵ `zr_leftWrite_pre` | 3 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 47 | 64% (358/563) | `zr_leftMove_fields` ⟵ `zr_return_bounds` | 2 | contract-opening, field-branches | differ | 183: `,Contract.ofSegment_post,skipTM_contract_lo,skipTM_contract_` |
| 48 | 64% (108/168) | `zr_leftPass_fields` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 49 | 64% (75/117) | `zr_loop_orbit` ⟵ `zr_loopAt_fields` | 1 | field-branches | differ | 40: `simponly[zr_loopAt,Function.update_self]` |
| 50 | 64% (107/168) | `zr_rightLeftFinal_link` ⟵ `zr_leftWrite_pre` | 3 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 51 | 64% (94/148) | `zr_rightPass_time` ⟵ `zr_return_time` | 1 | contract-opening | differ | 37: `Contract,Contract.ofSegment_time,zr_r` |
| 52 | 64% (107/168) | `zr_rightRuler_write_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 53 | 64% (296/461) | `zr_twoSteps_fields` ⟵ `zr_return_post` | 2 | contract-opening, field-branches | differ | 92: `ost]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some` |
| 54 | 64% (293/461) | `zr_writeHalves_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 95: `t_post]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_s` |
| 55 | 63% (347/554) | `zr_adjustedBack_post` ⟵ `zr_body_post` | 1 | contract-opening, field-branches | differ | 120: `e]·simponly[Cfg.mapState_inputPos,seekPost_inputPos]·funextj` |
| 56 | 63% (114/182) | `zr_extend_pre` ⟵ `zr_rightReturn_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 57 | 63% (937/1487) | `zr_final_fields` ⟵ `zr_leftMove_fields` | 3 | contract-opening, field-branches, arithmetic-ledger, word-reading | differ | 110: `Cfg.mapState_workTapePos,seekPost_workTapePos,Function.updat` |
| 58 | 63% (354/563) | `zr_final_fields` ⟵ `zr_return_bounds` | 3 | contract-opening, field-branches | differ | 134: `,Cfg.mapState_workTapePos,seekPost_workTapePos,Function.upda` |
| 59 | 63% (309/494) | `zr_return_bounds` ⟵ `zr_body_bounds` | 1 | contract-opening, field-branches, arithmetic-ledger | differ | 154: `ost,Cfg.mapState_workTapePos,seekPost_workTapePos,Function.u` |
| 60 | 63% (114/182) | `zr_rightLeft_pre` ⟵ `zr_rightReturn_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 61 | 63% (115/182) | `zr_rightReturn_post` ⟵ `zr_rightReturn_pre` | 1 | contract-opening, field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 62 | 63% (114/181) | `zr_rightReturn_pre` ⟵ `zr_extend_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 63 | 63% (106/168) | `zr_writeHalves_post` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 50: `t,Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 64 | 62% (127/206) | `zr_final_fields` ⟵ `zr_leftMove_pre` | 3 | contract-opening, field-branches | differ | 51: `Contract,zr_reindexContract,Contract.ofSegment_pre]` |
| 65 | 62% (287/460) | `zr_final_fields` ⟵ `zr_rightLeftFinal_link` | 3 | contract-opening, field-branches | differ | 99: `rw[zr_finalContract,Contract.seq_pre,zr_finalSeekContract,zr` |
| 66 | 62% (127/206) | `zr_leftPass_fields` ⟵ `zr_leftMove_pre` | 2 | contract-opening, field-branches | differ | 51: `Contract,zr_reindexContract,Contract.ofSegment_pre]` |
| 67 | 62% (273/438) | `zr_leftWriteContract` ⟵ `zr_leftPassContract` | 2 | contract-opening, field-branches, zoneRowPre-reading | same binders; types inferred | 73: `(funr=>?_)?_<;>simponly[Cfg.mapState_workTapes,Cfg.mapState_` |
| 68 | 62% (285/461) | `zr_leftWrite_fields` ⟵ `zr_return_post` | 2 | contract-opening, field-branches | differ | 94: `_post]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_so` |
| 69 | 62% (112/182) | `zr_rightReturn_bounds` ⟵ `zr_rightReturn_pre` | 1 | contract-opening, field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 70 | 62% (94/151) | `zr_seekStart_pre` ⟵ `zr_left_reach` | 2 | arithmetic-ledger | differ | 56: `:zoneStart0=2:=bynorm_num[zoneStart_eq]rw[Nat.sub_self,h` |
| 71 | 61% (72/118) | `zr_fintypeLoopPh` ⟵ `zr_decEqLoopPh` | 3 | instance-plumbing | differ | 36: `(OptionBool))\|true=>inferInstanceAs(` |
| 72 | 61% (190/310) | `zr_leftMove_fields` ⟵ `zr_leftMove_link₁` | 2 | contract-opening, field-branches | differ | 87: `zr_scratchSkipContract,zr_reindexContract,Contract.ofSegment` |
| 73 | 61% (62/101) | `zr_leftWalk_fields` ⟵ `zr_test_time` | 2 | contract-opening | differ | 36: `,zr_stepContract,Contract.ofSegment_` |
| 74 | 61% (126/206) | `zr_rightLeftFinal_link` ⟵ `zr_leftMove_pre` | 3 | contract-opening, field-branches | differ | 50: `Contract,zr_reindexContract,Contract.ofSegment_pre` |
| 75 | 61% (110/181) | `zr_rightPass_pre` ⟵ `zr_extend_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 76 | 61% (114/186) | `zr_rightReturn_pre` ⟵ `zr_rightLeft_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 77 | 60% (277/460) | `zr_leftPass_fields` ⟵ `zr_rightLeftFinal_link` | 3 | contract-opening, field-branches | differ | 70: `,Function.update_of_ne(bydecide:(1:Fin2)≠0),show(1:Fin2)≠0by` |
| 78 | 60% (619/1039) | `zr_leftWrite_fields` ⟵ `zr_twoSteps_fields` | 2 | contract-opening, field-branches | differ | 112: `]ring·simponly[Cfg.mapState_workTapePos,Function.update_of_n` |
| 79 | 60% (353/585) | `zr_rightPass_post` ⟵ `zr_test_post` | 1 | contract-opening, field-branches | differ | 90: `]·simponly[Function.update_of_nehj,Cfg.mapState_workTapePos]` |
| 80 | 60% (110/182) | `zr_rightPass_pre` ⟵ `zr_rightReturn_pre` | 1 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 81 | 60% (332/554) | `zr_rightRuler_post` ⟵ `zr_body_post` | 1 | contract-opening, field-branches | differ | 73: `Post_inputPos]·funextjqsimponly[Cfg.mapState_workTapes,seekP` |
| 82 | 59% (344/585) | `zr_adjustedWalk_post` ⟵ `zr_test_post` | 1 | contract-opening, field-branches | differ | 91: `t_post,zr_cellContract,zr_cellPost]applyCfg.ext·simponly[Cfg` |
| 83 | 59% (328/554) | `zr_return_post` ⟵ `zr_body_post` | 1 | contract-opening, field-branches | differ | 197: `e]·simponly[Cfg.mapState_inputPos,seekPost_inputPos]·funextj` |
| 84 | 59% (83/140) | `zr_rightLeft_link` ⟵ `zr_rightPass_pre` | 2 | contract-opening, field-branches | differ | 49: `,Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 85 | 59% (110/186) | `zr_rightPass_pre` ⟵ `zr_rightLeft_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 84: `_pre]simponly[zoneRowPre,funext_iff,Cfg.mapState_workTapes,C` |
| 86 | 59% (272/462) | `zr_rightSeekBack_ruler_pre` ⟵ `zr_rightSeek_back_pre` | 1 | contract-opening, field-branches, zoneRowPre-reading | differ | 102: `TM_contract_pre]introphlefthrightsimponly[Cfg.mapState_workT` |
| 87 | 58% (81/140) | `zr_leftPass_fields` ⟵ `zr_rightPass_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 88 | 57% (104/181) | `zr_extend_fields` ⟵ `zr_extend_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 89 | 57% (137/239) | `zr_loop_home_test` ⟵ `zr_loop_home_word` | 1 | field-branches, arithmetic-ledger, word-reading | differ | 72: `haveh0:zoneStart0=2:=bynorm_num[zoneStart_eq]havehL:=two_le_` |
| 90 | 57% (104/181) | `zr_rightLeft_fields` ⟵ `zr_extend_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 91 | 57% (103/181) | `zr_rightLeft_post` ⟵ `zr_extend_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 92 | 57% (263/461) | `zr_rightPass_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 90: `t]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some]·` |
| 93 | 56% (104/186) | `zr_extend_fields` ⟵ `zr_rightLeft_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 94 | 56% (211/376) | `zr_finalContract` ⟵ `zr_returnContract` | 3 | contract-opening, field-branches | same binders; types inferred | 57: `simponly[Cfg.mapState_workTapes,Cfg.mapState_workTapePos,` |
| 95 | 56% (1191/2137) | `zr_final_fields` ⟵ `zr_leftPass_fields` | 3 | contract-opening, field-branches, phase-literals | differ | 134: `,Cfg.mapState_workTapePos,seekPost_workTapePos,Function.upda` |
| 96 | 56% (581/1036) | `zr_leftMove_fields` ⟵ `zr_adjustedBack_post` | 2 | contract-opening, field-branches, arithmetic-ledger | differ | 161: `_state,Option.map_some]·simponly[Cfg.mapState_inputPos,seekP` |
| 97 | 56% (78/140) | `zr_leftMove_pre` ⟵ `zr_rightPass_pre` | 2 | contract-opening, field-branches | differ | 49: `,Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 98 | 56% (640/1142) | `zr_leftWriteContract` ⟵ `zr_leftMoveContract` | 2 | contract-opening, field-branches, zoneRowPre-reading | same binders; types inferred | 122: `d).2.1]refinezr_scratchAt_move__hp(funr=>?_)?_<;>simponly[Cf` |
| 99 | 56% (78/140) | `zr_leftWrite_pre` ⟵ `zr_rightPass_pre` | 2 | contract-opening, field-branches | differ | 49: `,Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 100 | 56% (104/186) | `zr_rightLeft_fields` ⟵ `zr_rightLeft_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 101 | 56% (78/140) | `zr_rightReturn_link` ⟵ `zr_rightPass_pre` | 1 | contract-opening, field-branches | differ | 48: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 102 | 56% (260/461) | `zr_test_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 60: `ost]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some` |
| 103 | 55% (267/486) | `zr_adjustedBack_post` ⟵ `zr_adjustedWalk_back_pre` | 2 | contract-opening, field-branches | differ | 132: `hprw[zr_adjustedWalkContract,Contract.ofSegment_pre,Contract` |
| 104 | 55% (309/563) | `zr_body_bounds` ⟵ `zr_return_bounds` | 1 | contract-opening, field-branches, arithmetic-ledger | differ | 154: `ost,Cfg.mapState_workTapePos,seekPost_workTapePos,Function.u` |
| 105 | 55% (102/186) | `zr_final_fields` ⟵ `zr_singleton_fields` | 3 | contract-opening | differ | 46: `t,Contract.ofSegment_lo,Contract.ofSegment_hi,` |
| 106 | 55% (240/438) | `zr_leftMoveContract` ⟵ `zr_leftPassContract` | 2 | contract-opening, field-branches, zoneRowPre-reading | same binders; types inferred | 72: `(funr=>?_)?_<;>simponly[Cfg.mapState_workTapes,Cfg.mapState_` |
| 107 | 55% (81/148) | `zr_leftMove_fields` ⟵ `zr_return_time` | 2 | contract-opening | differ | 53: `Contract,Contract.ofSegment_time,skipTM_contract_time` |
| 108 | 55% (102/186) | `zr_leftPass_fields` ⟵ `zr_singleton_fields` | 2 | contract-opening | differ | 46: `t,Contract.ofSegment_lo,Contract.ofSegment_hi,` |
| 109 | 55% (309/563) | `zr_rightPass_bounds` ⟵ `zr_return_bounds` | 1 | contract-opening, field-branches | differ | 57: `Contract,Contract.ofSegment_lo,Contract.ofSegment_hi,zr_r` |
| 110 | 55% (324/585) | `zr_rightRuler_post` ⟵ `zr_test_post` | 1 | contract-opening, field-branches | differ | 58: `·simponly[Function.update_of_nehj,Cfg.mapState_workTapePos` |
| 111 | 55% (323/585) | `zr_twoSteps_fields` ⟵ `zr_test_post` | 2 | contract-opening, field-branches | differ | 96: `e]·simponly[Cfg.mapState_inputPos]·funextjqsimponly[Cfg.mapS` |
| 112 | 54% (75/140) | `zr_extend_fields` ⟵ `zr_rightPass_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 113 | 54% (76/140) | `zr_final_fields` ⟵ `zr_rightPass_pre` | 3 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 114 | 54% (559/1039) | `zr_final_fields` ⟵ `zr_twoSteps_fields` | 3 | contract-opening, field-branches | differ | 66: `_workTapePos,Function.update_of_nehj]·simponly[Cfg.mapState_` |
| 115 | 54% (63/116) | `zr_halfWriteContract` ⟵ `zr_scratchSkipContract` | 2 | zoneRowPre-reading | differ | 63: `x)(funn=>List.replicaten(Sum.inlfalse))(funnd=>zr_scratchAt0` |
| 116 | 54% (100/186) | `zr_leftMove_fields` ⟵ `zr_singleton_fields` | 2 | contract-opening | differ | 46: `t,Contract.ofSegment_lo,Contract.ofSegment_hi,` |
| 117 | 54% (797/1487) | `zr_leftPass_fields` ⟵ `zr_leftMove_fields` | 2 | contract-opening, field-branches | differ | 116: `TM_contract_post,Cfg.mapState_workTapePos,seekPost_workTapeP` |
| 118 | 54% (100/186) | `zr_leftWalk_fields` ⟵ `zr_singleton_fields` | 2 | contract-opening | differ | 46: `t,Contract.ofSegment_lo,Contract.ofSegment_hi,` |
| 119 | 54% (100/186) | `zr_leftWrite_fields` ⟵ `zr_singleton_fields` | 2 | contract-opening | differ | 46: `t,Contract.ofSegment_lo,Contract.ofSegment_hi,` |
| 120 | 54% (187/346) | `zr_loop_zone_word` ⟵ `zr_loop_zone_test` | 1 | field-branches, arithmetic-ledger | differ | 73: `havehs:=zoneStart_succi.valhavehm:=zoneStart_mono(showi.val+` |
| 121 | 54% (76/140) | `zr_rightLeftFinal_link` ⟵ `zr_rightPass_pre` | 3 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 122 | 54% (75/140) | `zr_rightLeft_fields` ⟵ `zr_rightPass_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 123 | 54% (75/140) | `zr_rightLeft_post` ⟵ `zr_rightPass_pre` | 3 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 124 | 54% (88/164) | `zr_rightReturnRow` ⟵ `zr_rightLeftRow` | 3 | contract-opening, instance-plumbing, phase-literals | same binders; types inferred | 33: `))set_optionsynthInstance.maxSize` |
| 125 | 54% (75/140) | `zr_rightReturn_bounds` ⟵ `zr_rightPass_pre` | 1 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 126 | 54% (75/140) | `zr_rightReturn_post` ⟵ `zr_rightPass_pre` | 1 | field-branches, zoneRowPre-reading | differ | 75: `only[zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapSta` |
| 127 | 54% (318/585) | `zr_rightSeekBack_post` ⟵ `zr_test_post` | 1 | contract-opening, field-branches | differ | 59: `]·simponly[Function.update_of_nehj,Cfg.mapState_workTapePos` |
| 128 | 53% (293/554) | `zr_final_fields` ⟵ `zr_body_post` | 3 | field-branches | differ | 62: `Cfg.mapState_workTapePos,seekPost_workTapePos,Function.updat` |
| 129 | 53% (311/585) | `zr_final_fields` ⟵ `zr_test_post` | 3 | contract-opening, field-branches | differ | 48: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos,` |
| 130 | 53% (188/358) | `zr_innerCopy_adjusted_pre` ⟵ `zr_leftWalk_pre` | 2 | contract-opening, field-branches | differ | 131: `zr_adjustedWalkContract,Contract.ofSegment_pre,Contract.seq_` |
| 131 | 53% (263/494) | `zr_leftPass_fields` ⟵ `zr_body_bounds` | 2 | contract-opening, field-branches | differ | 154: `ost,Cfg.mapState_workTapePos,seekPost_workTapePos,Function.u` |
| 132 | 53% (100/189) | `zr_leftWalk_pre` ⟵ `zr_rightRuler_pre` | 2 | contract-opening, field-branches | differ | 53: `Contract,Contract.ofSegment_pre,Contract.seq_pre,zr_r` |
| 133 | 53% (296/554) | `zr_leftWrite_fields` ⟵ `zr_body_post` | 2 | field-branches | differ | 56: `applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some` |
| 134 | 53% (74/140) | `zr_loop_round` ⟵ `zr_rightPass_pre` | 1 | contract-opening, field-branches | differ | 48: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 135 | 53% (291/554) | `zr_rightLeft_post` ⟵ `zr_body_post` | 3 | contract-opening, field-branches | differ | 56: `applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some` |
| 136 | 53% (96/181) | `zr_rightSeekBack_ruler_pre` ⟵ `zr_extend_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 70: `zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapState_wo` |
| 137 | 53% (109/206) | `zr_rightSeekBack_ruler_pre` ⟵ `zr_leftMove_pre` | 2 | contract-opening, field-branches | differ | 49: `,Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 138 | 53% (96/182) | `zr_rightSeekBack_ruler_pre` ⟵ `zr_rightReturn_pre` | 1 | contract-opening, field-branches, zoneRowPre-reading | differ | 70: `zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapState_wo` |
| 139 | 53% (89/168) | `zr_rulerStep_walk_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 49: `t,Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 140 | 52% (87/168) | `zr_adjustedBack_copy_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 141 | 52% (87/168) | `zr_adjustedWalk_back_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 142 | 52% (87/168) | `zr_innerCopy_adjusted_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 143 | 52% (195/376) | `zr_leftMoveContract` ⟵ `zr_returnContract` | 2 | contract-opening, field-branches | same binders; types inferred | 57: `simponly[Cfg.mapState_workTapes,Cfg.mapState_workTapePos,` |
| 144 | 52% (258/494) | `zr_leftMove_fields` ⟵ `zr_body_bounds` | 2 | contract-opening, field-branches | differ | 110: `Cfg.mapState_workTapePos,seekPost_workTapePos,Function.updat` |
| 145 | 52% (240/460) | `zr_leftMove_fields` ⟵ `zr_rightLeftFinal_link` | 3 | contract-opening, field-branches | differ | 48: `Contract,zr_reindexContract,Contract.ofSegment_p` |
| 146 | 52% (537/1039) | `zr_leftMove_fields` ⟵ `zr_twoSteps_fields` | 2 | contract-opening, field-branches | differ | 92: `ost]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some` |
| 147 | 52% (87/168) | `zr_leftWalk_pre` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 148 | 52% (207/398) | `zr_leftWriteContract` ⟵ `zr_twoStepsContract` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 143: `refinezr_scratchAt_move__hp(funr=>?_)?_<;>simponly[zr_cellCo` |
| 149 | 52% (87/168) | `zr_return_bounds` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 33: `pContract,Contract.ofSegment_pre]` |
| 150 | 52% (242/461) | `zr_rightLeft_post` ⟵ `zr_return_post` | 3 | contract-opening, field-branches | differ | 89: `applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some]·si` |
| 151 | 52% (108/206) | `zr_rightReturn_link` ⟵ `zr_leftMove_pre` | 2 | contract-opening, field-branches | differ | 48: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 152 | 52% (77/148) | `zr_rightReturn_link` ⟵ `zr_return_time` | 1 | contract-opening | differ | 43: `e,zr_returnSkipContract,Contract.ofSegment_` |
| 153 | 52% (242/461) | `zr_rightReturn_post` ⟵ `zr_return_post` | 1 | contract-opening, field-branches | differ | 90: `]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some]·s` |
| 154 | 52% (107/206) | `zr_rightRuler_write_pre` ⟵ `zr_leftMove_pre` | 2 | contract-opening, field-branches | differ | 47: `Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 155 | 52% (96/186) | `zr_rightSeekBack_ruler_pre` ⟵ `zr_rightLeft_pre` | 3 | contract-opening, field-branches, zoneRowPre-reading | differ | 70: `zoneRowPre,funext_iff,Cfg.mapState_workTapes,Cfg.mapState_wo` |
| 156 | 51% (181/358) | `zr_adjustedBack_copy_pre` ⟵ `zr_leftWalk_pre` | 2 | contract-opening, field-branches | differ | 124: `zr_adjustedWalkContract,Contract.ofSegment_pre,Contract.seq_` |
| 157 | 51% (184/358) | `zr_adjustedBack_post` ⟵ `zr_leftWalk_pre` | 2 | contract-opening, field-branches | differ | 127: `rw[zr_adjustedWalkContract,Contract.ofSegment_pre,Contract.s` |
| 158 | 51% (184/358) | `zr_adjustedWalk_back_pre` ⟵ `zr_leftWalk_pre` | 2 | contract-opening, field-branches | differ | 127: `rw[zr_adjustedWalkContract,Contract.ofSegment_pre,Contract.s` |
| 159 | 51% (190/376) | `zr_leftPassContract` ⟵ `zr_returnContract` | 2 | contract-opening, field-branches | same binders; types inferred | 113: `simponly[Cfg.mapState_workTapes,Cfg.mapState_workTapePos,see` |
| 160 | 51% (473/923) | `zr_leftPass_fields` ⟵ `zr_rightSeekBack_post` | 2 | contract-opening, field-branches | differ | 81: `_state,Option.map_some]·simponly[Cfg.mapState_inputPos,seekP` |
| 161 | 51% (296/585) | `zr_leftPass_fields` ⟵ `zr_test_post` | 2 | contract-opening, field-branches | differ | 56: `applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some` |
| 162 | 51% (192/376) | `zr_leftWriteContract` ⟵ `zr_returnContract` | 2 | contract-opening, field-branches | same binders; types inferred | 58: `simponly[Cfg.mapState_workTapes,Cfg.mapState_workTapePos,s` |
| 163 | 51% (756/1487) | `zr_leftWrite_fields` ⟵ `zr_leftMove_fields` | 2 | contract-opening, field-branches, arithmetic-ledger, word-reading | differ | 94: `_post]applyCfg.ext·simponly[Cfg.mapState_state,Option.map_so` |
| 164 | 51% (288/563) | `zr_leftWrite_fields` ⟵ `zr_return_bounds` | 2 | contract-opening, field-branches | differ | 77: `_workTapePos,Function.update_self,Function.update_of_ne(byde` |
| 165 | 51% (137/270) | `zr_loop_home_word` ⟵ `zr_loop_home_test` | 1 | field-branches, arithmetic-ledger, word-reading | differ | 72: `haveh0:zoneStart0=2:=bynorm_num[zoneStart_eq]havehL:=two_le_` |
| 166 | 51% (282/554) | `zr_rightReturn_post` ⟵ `zr_body_post` | 1 | contract-opening, field-branches | differ | 56: `applyCfg.ext·simponly[Cfg.mapState_state,Option.map_some` |
| 167 | 51% (121/239) | `zr_rightWord_word` ⟵ `zr_loop_home_word` | 1 | arithmetic-ledger, word-reading | differ | 66: `,List.length_singleton,h0]ath2⊢rw[show((2:ℕ):ℤ)-(1:ℕ)-1+p=pb` |
| 168 | 51% (85/168) | `zr_test_post` ⟵ `zr_leftWrite_pre` | 2 | contract-opening, field-branches | differ | 48: `,Cfg.mapState_workTapes,Cfg.mapState_workTapePos` |
| 169 | 51% (106/206) | `zr_writeHalves_post` ⟵ `zr_leftMove_pre` | 2 | contract-opening, field-branches | differ | 50: `t,Cfg.mapState_workTapes,Cfg.mapState_workTapePos]` |
| 170 | 51% (296/585) | `zr_writeHalves_post` ⟵ `zr_test_post` | 1 | contract-opening, field-branches | differ | 74: `e]·simponly[Cfg.mapState_inputPos]·funextjqsimponly[Cfg.mapS` |
| 171 | 50% (303/605) | `zr_adjustedBack_post` ⟵ `zr_innerCopy_adjusted_pre` | 2 | contract-opening, field-branches | differ | 124: `zr_adjustedWalkContract,Contract.ofSegment_pre,Contract.seq_` |
| 172 | 50% (764/1521) | `zr_final_fields` ⟵ `zr_leftWrite_fields` | 3 | contract-opening, field-branches, arithmetic-ledger, word-reading | differ | 97: `_workTapes,hj,false_and,if_false]·funextjby_caseshj:j=0·subs` |
| 173 | 50% (70/140) | `zr_rightPass_time_le` ⟵ `zr_extend_time_le` | 3 | arithmetic-ledger | differ | 70: `byhaveh:=zr_extent_costD.1havehm:=zoneStart_mono(Nat.le_add_` |
