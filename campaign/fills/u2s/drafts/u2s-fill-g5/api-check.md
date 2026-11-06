# API check for `u2s-fill-g5.DRAFT.md`

Every declaration the draft cites, with the file and line where it is declared, read with
`git show <ref>:<path>` (no build) at two refs:

- **#197**: `origin/pr/197`, `fde50a5a72c7dfa34699a2968255a67dec1965ef`;
- **the campaign tip**: `0d2b3bbd7a23a5d5cefe50c00b4ea6857fd28d8a`, after #197's merge
  `33ceeed161301fa5147826c25d40265e3d7528a5` (2026-11-05,
  during the drafting; `git diff origin/pr/197 HEAD -- TCSlib` is empty there).

**Every line below is the same at both refs** (177 rows checked by script). At the pre-merge tip
`9859c8100983b1200d744298443291bff2144266`, where the drafting started, the #197 names were absent.

Paths are relative to `TCSlib/Complexity/TuringMachine/`. A line given for a `simps`-generated
name is the `attribute [simps …]` line that generates it; gate 97's closing axiom probe
(`campaign/gates/97-zone-step-api/evidence/closing/axioms/Ax.out`) prints every #197 field
equation by name. Where a search matched two declarations (`Segment.trans` and `Segment.mono`, in
the `Segment` and `SafeSegment` namespaces) the first is the cited one; each hit's namespace was
checked against the enclosing `namespace` lines.

**Result: every cited TCSlib declaration exists at #197 and at the merged tip**, except the two
WS-1 canonical lemmas, which exist only on #196 (below; the draft marks them `@TBD@`), and three
probe-only names, which the draft cites only as names not to rebuild.

## G5's consumer API: `Build/ZoneStep` (new in #197)

- `Turing.exists_zoneTrackStepTM` (theorem): `Build/ZoneStep.lean:109`.
- `Turing.zoneTrackStepData` (def): `Build/ZoneStep.lean:62`.
- `Turing.zoneTrackStepData_of_lt` (theorem): `Build/ZoneStep.lean:67`.
- `Turing.zoneTrackStepData_of_not_lt` (theorem): `Build/ZoneStep.lean:73`.
- `Turing.sum_two_pow_le_of_count` (theorem): `Build/ZoneStep.lean:251`.
- `Turing.sum_cost_le_of_count` (theorem): `Build/ZoneStep.lean:298`.
- `zs_rowPre_rebalancePost (private)` (private (hazard)): `Build/ZoneStep.lean:79`.

## The rows and their equations: `Build/ZoneRebalance`

- `Turing.ZoneData` (abbrev): `Build/ZoneRebalance.lean:78`.
- `Turing.zoneRowPre` (def): `Build/ZoneRebalance.lean:84`.
- `Turing.zoneRowPre_iff` (theorem): `Build/ZoneRebalance.lean:144`.
- `Turing.zoneRowPre_congr` (theorem): `Build/ZoneRebalance.lean:153`.
- `Turing.zoneRowPre_mapState_iff` (theorem): `Build/ZoneRebalance.lean:161`.
- `Turing.zoneRebalanceIndex` (def): `Build/ZoneRebalance.lean:89`.
- `Turing.zoneRebalanceIndex_eq` (theorem): `Build/ZoneRebalance.lean:169`.
- `Turing.zoneRebalanceIndex_le` (theorem): `Build/ZoneRebalance.lean:174`.
- `Turing.zoneRebalanceData` (def): `Build/ZoneRebalance.lean:94`.
- `Turing.zoneExtendData` (def): `Build/ZoneRebalance.lean:99`.
- `Turing.zoneRebalancePost` (def): `Build/ZoneRebalance.lean:106`.
- `Turing.zoneExtendPost` (def): `Build/ZoneRebalance.lean:115`.
- `Turing.zoneRebalanceData_fst`, `_snd`, `Turing.zoneExtendData_fst`, `_snd`, and the fields
  `Turing.zoneRebalancePost_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output` and the
  same five of `Turing.zoneExtendPost` (simps; all 14 printed by gate 97's closing axiom probe):
  `Build/ZoneRebalance.lean:139`.
- `Turing.zoneRebalanceData_of_short` (theorem): `Build/ZoneRebalance.lean:15309`.
- `Turing.zoneRebalanceIndex_extend_of_short` (theorem): `Build/ZoneRebalance.lean:15320`.
- `Turing.exists_zoneRebalanceTM` (theorem): `Build/ZoneRebalance.lean:15170`.
- `Turing.exists_zoneExtendTM` (theorem): `Build/ZoneRebalance.lean:15224`.
- `zr_exitsContract (private)` (private (hazard)): `Build/ZoneRebalance.lean:181`.
- `zr_singletonContract (private)` (private (hazard)): `Build/ZoneRebalance.lean:190`.

## The carrier: `Build/ZoneTape`

- `Turing.ZoneCell` (abbrev): `Build/ZoneTape.lean:78`.
- `Turing.ZoneSym` (abbrev): `Build/ZoneTape.lean:85`.
- `Turing.zoneCellOfCell` (def): `Build/ZoneTape.lean:105`.
- `Turing.zoneCellOfCell_inr` (theorem): `Build/ZoneTape.lean:111`.
- `Turing.zoneCellOfCell_inl` (theorem): `Build/ZoneTape.lean:116`.
- `Turing.zoneCellOfCell_none` (theorem): `Build/ZoneTape.lean:122`.
- `Turing.zoneStart_eq` (theorem): `Build/ZoneTape.lean:164`.
- `Turing.zonedTape` (def): `Build/ZoneTape.lean:285`.
- `Turing.zonedTape_zero` (theorem (@[simp])): `Build/ZoneTape.lean:310`.
- `Turing.zonedTape_blank_outside` (theorem): `Build/ZoneTape.lean:360`.
- `Turing.zonedTape_homeWrite` (theorem): `Build/ZoneTape.lean:459`.

## The pure layer: `Build/Zone`

- `Turing.zoneCapacity_eq` (theorem): `Build/Zone.lean:103`.
- `Turing.ZoneContents` (structure): `Build/Zone.lean:154`.
- `Turing.ZoneContents.empty` (def): `Build/Zone.lean:188`.
- `Turing.ZoneContents.empty_home, _left, _right` (simps): `Build/Zone.lean:195`.
- `Turing.ZoneContents.words_true` (theorem): `Build/Zone.lean:1056`.
- `Turing.ZoneContents.words_false` (theorem): `Build/Zone.lean:1061`.
- `Turing.ZoneContents.extend` (def): `Build/Zone.lean:1294`.
- `Turing.ZoneContents.extend_words_castSucc` (theorem): `Build/Zone.lean:1314`.
- `Turing.ZoneContents.extend_words_last` (theorem): `Build/Zone.lean:1319`.
- `Turing.zoneHomeWrite` (def): `Build/Zone.lean:462`.
- `Turing.zoneHomeWrite_home, _left, _right` (simps): `Build/Zone.lean:465`.
- `Turing.zoneShiftIndex_le` (theorem): `Build/Zone.lean:1164`.
- `Turing.zoneShiftIndex_empty` (theorem): `Build/Zone.lean:1173`.
- `Turing.zoneShiftIndex_nonempty` (theorem): `Build/Zone.lean:1184`.
- `Turing.zoneShiftIndex_eq` (theorem): `Build/Zone.lean:1198`.
- `Turing.zoneShiftIndex_eq_length_iff` (theorem): `Build/Zone.lean:1211`.
- `Turing.zoneShiftIndex_extend` (theorem): `Build/Zone.lean:1339`.
- `Turing.zoneShiftIndex_extend_of_lt` (theorem): `Build/Zone.lean:1355`.
- `Turing.zoneRebalance_of_lt` (theorem): `Build/Zone.lean:1236`.
- `Turing.zoneRebalance_of_le` (theorem): `Build/Zone.lean:1229`.
- `Turing.zoneRebalance_frame` (theorem): `Build/Zone.lean:1273`.
- `Turing.zoneCascade_true` (theorem): `Build/Zone.lean:1139`.
- `Turing.zoneCascade_false` (theorem): `Build/Zone.lean:1145`.
- `Turing.zoneCascadeRight_lengths` (theorem): `Build/Zone.lean:848`.
- `Turing.zoneCascadeLeft_lengths` (theorem): `Build/Zone.lean:1121`.
- `Turing.zoneTrackTape_zero` (theorem): `Build/Zone.lean:1378`.
- `Turing.zoneTrackTape_empty` (theorem): `Build/Zone.lean:1399`.
- `Turing.zoneTrackTape_homeWrite` (theorem): `Build/Zone.lean:1444`.
- `Turing.zoneTrackTape_extend` (theorem): `Build/Zone.lean:1425`.
- `Turing.zoneTrackTape_rebalance_right` (theorem): `Build/Zone.lean:1551`.
- `Turing.zoneTrackTape_rebalance_left` (theorem): `Build/Zone.lean:1568`.
- `Turing.ZoneContents.words` (def): `Build/Zone.lean:1051`.
- `Turing.zoneCapacity` (def): `Build/Zone.lean:99`.
- `Turing.zoneCascade` (def): `Build/Zone.lean:1134`.
- `Turing.zoneRebalance` (def): `Build/Zone.lean:1225`.
- `Turing.zoneShiftIndex` (def): `Build/Zone.lean:1153`.
- `Turing.zoneTrackTape` (def): `Build/Zone.lean:1371`.

## Contracts, segments, rounds, lockstep: `Build/Contract/Basic`

- `Turing.Contract` (structure): `Build/Contract/Basic.lean:143`.
- `Turing.Contract.live` (theorem): `Build/Contract/Basic.lean:251`.
- `Turing.Contract.segment` (theorem): `Build/Contract/Basic.lean:608`.
- `Turing.Contract.ofSegment` (def): `Build/Contract/Basic.lean:616`.
- `Turing.Contract.ofSegment_pre … _hi` (simps): `Build/Contract/Basic.lean:634`.
- `Turing.Contract.zero` (def): `Build/Contract/Basic.lean:639`.
- `Turing.Contract.zero_pre` (theorem): `Build/Contract/Basic.lean:649`.
- `Turing.Contract.zero_time` (theorem): `Build/Contract/Basic.lean:654`.
- `Turing.Contract.zero_post` (theorem): `Build/Contract/Basic.lean:659`.
- `Turing.Contract.zero_lo` (theorem): `Build/Contract/Basic.lean:664`.
- `Turing.Contract.zero_hi` (theorem): `Build/Contract/Basic.lean:669`.
- `Turing.Contract.time_envelope` (theorem): `Build/Contract/Basic.lean:675`.
- `Turing.Contract.trans` (def): `Build/Contract/Basic.lean:205`.
- `Turing.Contract.trans_pre … _hi` (simps): `Build/Contract/Basic.lean:244`.
- `Turing.Segment` (def): `Build/Contract/Basic.lean:423`.
- `Turing.segment_iff` (theorem): `Build/Contract/Basic.lean:431`.
- `Turing.Segment.one` (theorem): `Build/Contract/Basic.lean:449`.
- `Turing.Segment.trans` (theorem): `Build/Contract/Basic.lean:463`.
- `Turing.Segment.mono` (theorem): `Build/Contract/Basic.lean:480`.
- `Turing.Segment.cons` (theorem): `Build/Contract/Basic.lean:521`.
- `Turing.Segment.live` (theorem): `Build/Contract/Basic.lean:536`.
- `Turing.Round` (def): `Build/Contract/Basic.lean:725`.
- `Turing.Round.iterate_seq` (theorem): `Build/Contract/Basic.lean:823`.
- `Turing.RoundContract` (structure): `Build/Contract/Basic.lean:856`.
- `Turing.Lockstep` (structure): `Build/Contract/Basic.lean:1305`.
- `Turing.Lockstep.runFrom` (theorem): `Build/Contract/Basic.lean:1323`.

## Seams and the phase-host contract: `Build/Contract/Seam`

- `Turing.Contract.seq` (def): `Build/Contract/Seam.lean:134`.
- `Turing.Contract.inPhase` (def): `Build/Contract/Seam.lean:268`.
- `Turing.Contract.branch` (def): `Build/Contract/Seam.lean:398`.
- `Turing.Contract.seq_*, inPhase_pre, inPhase_time, inPhase_post, branch_*` (simps):
  `Build/Contract/Seam.lean:536`.
- `Turing.Contract.seq_positive` (theorem): `Build/Contract/Seam.lean:795`.
- `Turing.Contract.inPhase_positive` (theorem): `Build/Contract/Seam.lean:805`.
- `Turing.Contract.branch_positive` (theorem): `Build/Contract/Seam.lean:814`.
- `Turing.Cfg.bindState` (def): `Build/Contract/Seam.lean:197`.
- `Turing.Cfg.bindState_state, _inputPos, _workTapes, _workTapePos, _output` (simps):
  `Build/Contract/Seam.lean:203`.

## The phase host: `Build/Seam`

- `Turing.phaseHostTM` (def): `Build/Seam.lean:835`.
- `Turing.phaseHostTM_tr_of_red_none` (theorem): `Build/Seam.lean:846`.
- `Turing.phaseHostTM_q₀` (theorem): `Build/Seam.lean:854`.
- `Turing.phaseHostTM_tr_of_red_some` (theorem): `Build/Seam.lean:861`.
- `Turing.phaseHostTM_run_le` (theorem): `Build/Seam.lean:876`.
- `Turing.phaseHostTM_run` (theorem): `Build/Seam.lean:898`.

## Configuration facts: `CfgFacts`

- `Turing.Cfg.mapState_eq_of_fields` (theorem): `CfgFacts.lean:69`.
- `Turing.Cfg.mapState_const_eq_mapState_sigma` (theorem): `CfgFacts.lean:87`.
- `Turing.Cfg.mapState_sigma_state_ne` (theorem): `CfgFacts.lean:101`.

## R1: `Build/Embed`

- `Turing.embedEmitTM` (def): `Build/Embed.lean:264`.
- `Turing.embedEmitTM_tr` (theorem): `Build/Embed.lean:281`.
- `Turing.embedEmitTM_runFrom` (theorem): `Build/Embed.lean:566`.
- `Turing.embedEmitTM_frame` (theorem): `Build/Embed.lean:582`.
- `Turing.embedEmitCfg_eq` (theorem): `Build/Embed.lean:1108`.

## The machine model: `Configuration`

- `Turing.Action.apply` (def (@[simp])): `Configuration.lean:244`.
- `Turing.Action.apply_state, _inputPos, _workTapePos, _output` (simps): `Configuration.lean:261`.
- `Turing.Cfg.inputSymbol_of_zero` (theorem): `Configuration.lean:207`.
- `Turing.Cfg.inputSymbol_of_end` (theorem): `Configuration.lean:213`.
- `Turing.inputSymbolInner` (lemma (@[simp])): `Configuration.lean:188`.
- `Turing.Cfg.workTapeSymbols_eq` (theorem): `Configuration.lean:221`.
- `Turing.Cfg.init_state, _inputPos, _workTapes, _workTapePos, _output` (simps):
  `Configuration.lean:236`.
- `Turing.moveInputPos` (def): `Configuration.lean:135`.
- `Turing.Cfg.ext (from @[ext] on Cfg)` (ext attribute (the next line declares Cfg)):
  `Configuration.lean:106`.
- `Turing.Cfg.init` (def): `Configuration.lean:230`.
- `Turing.Cfg.inputSymbol` (def): `Configuration.lean:178`.

## The machine model: `Simulation`

- `Turing.Action.apply_workTapes` (lemma): `Simulation.lean:89`.

## The machine model: `StateRenaming`

- `Turing.Cfg.mapState` (def): `StateRenaming.lean:87`.
- `Turing.Cfg.mapState_state, _inputPos, _workTapes, _workTapePos, _output` (simps):
  `StateRenaming.lean:97`.

## The machine model: `Deterministic`

- `Turing.MultiTapeTM.step_of_halt` (lemma): `Deterministic.lean:191`.
- `Turing.MultiTapeTM.step_of_some` (theorem): `Deterministic.lean:200`.
- `Turing.MultiTapeTM.runFrom_zero` (lemma): `Deterministic.lean:210`.
- `Turing.MultiTapeTM.runFrom_succ_eq_step'` (lemma): `Deterministic.lean:218`.
- `Turing.MultiTapeTM.runFrom_add` (lemma): `Deterministic.lean:223`.
- `Turing.MultiTapeTM.runFrom_of_halt` (lemma): `Deterministic.lean:262`.
- `Turing.MultiTapeTM.initCfg` (def): `Deterministic.lean:183`.
- `Turing.MultiTapeTM.initCfg_eq` (theorem): `Deterministic.lean:187`.
- `Turing.MultiTapeTM.step` (def): `Deterministic.lean:169`.
- `Turing.MultiTapeTM.runFrom` (def): `Deterministic.lean:207`.

## Bundled machines: `Finite`

- `Turing.MultiTapeTM.runFrom_state_ne_none_of_le` (theorem): `Finite.lean:201`.
- `Turing.MultiTapeTM.exists_first_halt` (theorem): `Finite.lean:218`.
- `Turing.MultiTapeTM.runFrom_with_q₀` (theorem): `Finite.lean:234`.
- `Turing.MultiTapeTM.initCfg_with_q₀` (theorem): `Finite.lean:241`.
- `Turing.FinTM` (structure): `Finite.lean:255`.
- `Turing.FinTM.ComputesInTime` (def): `Finite.lean:276`.
- `Turing.FinTM.computesFunInTime_iff` (theorem): `Finite.lean:289`.
- `Turing.FinTM.ComputesInTime.mono` (theorem): `Finite.lean:337`.
- `Turing.FinTM.not_computesInTime_zero` (theorem): `Finite.lean:350`.
- `Turing.FinTM.ComputesInTime.output_unique` (theorem): `Finite.lean:363`.
- `Turing.FinTM.computesInTime_iff` (theorem): `Finite.lean:383`.
- `Turing.FinTM.ComputesFunInTime` (def): `Finite.lean:281`.

## The finish: `Robustness/AlphabetReduction`

- `Turing.FinTM.alphabet_reduction_run` (theorem): `Robustness/AlphabetReduction.lean:618`.
- `arTM_computes (private)` (private (hazard)): `Robustness/AlphabetReduction.lean:547`.
- `arCfg_run (private)` (private (hazard)): `Robustness/AlphabetReduction.lean:502`.

## The target and its corollary: `Robustness/TwoTapes`

- `Turing.FinTM.two_work_tapes_run` (theorem (target)): `Robustness/TwoTapes.lean:64`.
- `Turing.FinTM.two_work_tapes_binary` (theorem): `Robustness/TwoTapes.lean:78`.

## The consumer: `UniversalTlogT`

- `Turing.universal_TlogT` (theorem): `UniversalTlogT.lean:57`.

## The consumer's input: `UniversalK`

- `Turing.universalK` (theorem): `UniversalK.lean:2764`.

## The six R3 rows the draft forbids citing (ground rule 11): `Build/Catalog`

- `Turing.copyTM_run` (theorem (R3 row, not to cite)): `Build/Catalog.lean:1758`.
- `Turing.transferTM_run` (theorem (R3 row, not to cite)): `Build/Catalog.lean:1671`.
- `Turing.clearTM_run` (theorem (R3 row, not to cite)): `Build/Catalog.lean:1832`.
- `Turing.compareTM_run` (theorem (R3 row, not to cite)): `Build/Catalog.lean:1900`.
- `Turing.incrementTM_run_succ` (theorem (R3 row, not to cite)): `Build/Catalog.lean:1982`.
- `Turing.incrementTM_run_overflow` (theorem (R3 row, not to cite)): `Build/Catalog.lean:2029`.

## Hazards named so as not to be copied (private): `Robustness/SingleTape`

- `unusedTapeTM (private)` (private (hazard)): `Robustness/SingleTape.lean:62`.
- `unusedTape_step (private)` (private (hazard)): `Robustness/SingleTape.lean:77`.
- `unusedTape_computes (private)` (private (hazard)): `Robustness/SingleTape.lean:95`.

## WS-1's canonical lemmas: only on #196 (not merged at drafting)

Not at #197 and not at the merged tip. On `origin/pr/196`,
`97adec6962e55c3a8ff191e602627674697fef18`:

- `Turing.Cfg.InWindow.apply_iff` (theorem): `Build/CfgRecord.lean:130`.
- `Turing.Cfg.InWindow.mono` (theorem): `Build/CfgRecord.lean:118`.

The draft cites them only in the WS-1 family bullet, marked `@TBD@` (whether the base has them).

## Probe-only names (not in the tree; cited only as "do not rebuild")

In `campaign/items/u2/probes/G5FitLanded.lean.txt`, namespace `Turing.G24Fit`:

- `trackStep_fit`, line 51; `amortized_le`, line 188; `run_cost_le`, line 226. Their public
  successors are `exists_zoneTrackStepTM`, `sum_two_pow_le_of_count` and `sum_cost_le_of_count`.

## Mathlib and core (mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, Lean v4.25.0)

- `Function.Embedding.inl` (def): `Mathlib/Logic/Embedding/Basic.lean:285` (`@[simps]` at 284).
- `Function.Embedding.inl_apply` (simps): generated by the `@[simps]` at
  `Mathlib/Logic/Embedding/Basic.lean:284`.
- `Nat.log` (def): `Mathlib/Data/Nat/Log.lean:34`.
- `Nat.pow_log_le_self` (theorem): `Mathlib/Data/Nat/Log.lean:116`.
- `Nat.lt_pow_succ_log_self` (theorem): `Mathlib/Data/Nat/Log.lean:134`.
- `Nat.log_mono_right` (theorem): `Mathlib/Data/Nat/Log.lean:188`.
- `Nat.log2_eq_log_two` (lemma): `Mathlib/Data/Nat/Log.lean:250`.
- `Fin.castLEEmb` (def): `Mathlib/Data/Fin/Embedding.lean:73`.
- `SignType` (inductive, deriving `DecidableEq`, `Inhabited`, `Fintype`):
  `Mathlib/Data/Sign/Defs.lean:20`.
- `lt_trichotomy` (lemma; a sweep sign): `Mathlib/Order/Defs/LinearOrder.lean:90`.
- `Nat.find` (def; a sweep sign): `Mathlib/Data/Nat/Find.lean:63`.
- `List.length_map` (theorem): Lean core, `Init/Data/List/Lemmas.lean:1051`.
- `List.getElem_map` (theorem): Lean core, `Init/Data/List/Lemmas.lean:1065`.
- `Nat.exists_eq_add_of_le` (theorem; a sweep sign): Lean core, `Init/Data/Nat/Lemmas.lean:385`.
- `Nat.log2` (def): Lean core, `Init/Data/Nat/Log2.lean:39`.

## Names in the draft that are not declarations

- `tt_`: the prefix proposed for the fill's privates; unused at the merged tip, at #197 and on all
  201 `origin/pr/*` heads (`git grep -E "\btt_[A-Za-z]"`).
- `HS`, `c₁`, `c₂`, `A`, `B`, `L`, `idx`, `cost`, `t₀`: the draft's names for the zone machine and
  the bound's terms, not Lean declarations.
- **The iteration lemma of `[Q2]`:** deliberately `@TBD@`; no such declaration exists and the draft
  names none. `Round.iterate_seq` and `Turing.Lockstep.runFrom` exist (above) and do not fit.
- Module names (`Build/ZoneStep`, …) and the campaign labels in the brief's prose (ZP-1, RN-1,
  WS-1, RI-1, FH-1, RS-1, RO-1; G5-F1; D1, D2) are records, not Lean.

## Could not find

None. Two searches needed correcting (`zoneShiftIndex_eq` and `zoneShiftIndex_extend`: the first
pattern wrongly required a word boundary before `{`); both are found at the lines above.
