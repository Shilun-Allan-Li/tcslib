# 09 Q-B1: the eight startup privates, verified independently

All at the base `6e8db28f` (= `77f1eb4f`), `TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean`
(2,325 lines; 3 public, 22 private). Direct TCSlib dependencies from the compiled module
(probe/KitDeps.lean, `getUsedConstants`), sizes with docstrings by line span.

| Private | Lines | Statement (short) | Direct TCSlib theorem dependencies | Uses in the core |
|---|---|---|---|---|
| `ic_header_result` | 101–131 (31) | `prefixCanonTM (pairExtractTM …)` on `⟨⟨bits t, α⟩, x⟩` halts by `16|bits t| + 8|α| + 25` with output `bits t`/`α`, head at `4|bits t| + 2|α| + 7` | `prefixCanon_complete`, `pairExtractTM_fst/_snd`, `pairDecode_pairEncode`, `length_pairEncode` | via `ic_header_capture` |
| `ic_capture_return` | 133–157 (25) | from a bounded halt of `M` on `x`, `embedSilentRetTM`'s first live return `u ≤ T`, configuration = the transport of the run at `T` | `exists_first_halt`, `embedSilentRetTM_run`, `initCfg_eq`, `Cfg.init_state` | via `ic_header_capture` |
| `ic_header_capture` | 199–240 (42) | either header pass, captured: first return ≤ the pass bound, head at the suffix, the selected word on `cap` at head `|w|`, frame kept, cut | the two above, `embedSilentCfg_cap/_inputPos/_output/_unselected` | 2 (998, 1130) |
| `ic_layout_call` | 242–293 (52) | `exists_seamLayoutTM` specialized to `serializeK M` at head 0: table and empty-output summary (`summaryCells none (unaryFin M.q₀)`), time `C·(|serializeK M|+1)` | `exists_seamLayoutTM`, **`serializeK_eq` (CodeSimulator)**, `unaryFin_eq`, `summaryCells_eq`, `bufferTape_of_neg` | 1 (919) |
| `ic_input_suffix` | 336–346 (11) | `(pairEncode u x).drop (2|u| + 2) = x` | `pairEncode_eq`, `length_pairEncode` | in `ic_window_call` |
| `ic_window_call` | 348–405 (58) | `exists_inputWindowCopyTM` on the nested input from the suffix: `x.take t` on a blank tape, cost `C·(min t |x| + 1) + 2|bits t|`, frame | `exists_inputWindowCopyTM`, `counterValue_eq/_bits`, `length_pairEncode`, `bufferTape_eq`, `ic_input_suffix` | 1 (915) |
| `ic_seam_step` | 719–743 (25) | `seamCompTM` run + exit state + inherited first-return cut, in one package | `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `Cfg.mapState_state` | 11 |
| `ic_install_phase` | 745–791 (47) | the install call embedded silently behind `seamReleaseTM`: positive first return at `T`, the transported endpoint | `embedSilentTM_runFrom`, `seamReleaseTM_runFrom_pos`, `embedSilentCfg_state`, `Cfg.ofWords_state`, `runFrom_zero`, `Cfg.mapState_state` | 1 (1618) |

Total 291 lines. None depends on another file's private; only `ic_layout_call` depends on
`CodeSimulator` (through `serializeK`/`serializeK_eq`).

## Does a published declaration already give any of them?
Fingerprint search with `git grep` over the tip `6e8db28f`, `origin/lean/phasehost-last`
(searched at `a4d9b024` and again at `0e5f210b`) and `origin/complexity/arora-barak-ch7`
(`a7433f3f`): the pass bound `16 * (Nat.bits t).length + 8 * α.length + 25`, `exists_first_halt`,
`seamCompTM_firstReturn_ofCfg`, `seamReleaseTM (embedSilentTM`, `exists_inputWindowCopyTM`,
`exists_seamLayoutTM`, `summaryCells none (unaryFin`, `drop (2 * u.length + 2)`,
`prefixCanon_complete`. Hits outside `NDCodeSimulator` and the rows' own files:
- `Complexity.Codec.pe_drop` (`SpaceComplexity/Codec/Parse.lean:69`, public): **exactly
  `ic_input_suffix`'s statement** (probe/PeDropProbe.lean: `pe_drop` has type
  `∀ u x, (pairEncode u x).drop (2 * u.length + 2) = x`), and
  `SpaceComplexity/Logspace/PathWalk.lean:225`'s private `drop_pairEncode` (the same statement).
  Citing `pe_drop` from `CodeSimulator` or from a kit module would import `Codec/Parse`, adding
  56 TCSlib modules (and its Mathlib roots) to `CodeSimulator`'s closure: not proportionate.
  A home beside `pairEncode_eq` in `Encoding` would retire all three, but `Encoding`'s downstream
  closure is 257 modules (mkdownmulti.py): a dedup-window item, as the report says.
- `Diagonalization/NTimeHierarchy`'s private `un_step` (255–274): the same statement as
  `ic_seam_step` (out/10). Not public.
- `UniversalK`'s privates (`ss_capturedPrefix_run`, `ss_serialized_layout`, `ss_capture_run`):
  related, different statements (out/10). Not public.
- No published equivalent of any of the eight. The PR heads add none (the ch7 head predates
  them).

## Would option B re-prove them, with cross-file pairs?
Yes. B5a's route needs each step (the two header passes and their capture, the window from the
suffix, the release-wrapped install, the layout of `serializeK M`, eleven seam joins). On the
published rows alone the fill must state and prove the same eight facts: a third private seam
package (after `ic_seam_step`, `un_step`), a third/fourth header capture (after R's, UN's,
U2-S's) and a fourth suffix drop. Short canonical proofs over the same rows reproduce at high
percentages (the v3 screen's ≥ 60-character, ≥ half rule), so cross-file pairs with
`NDCodeSimulator` (in the population) are near-certain; the draft's ⟨Q-B1: B⟩ already
pre-discloses them. `workflow.md` §4 ("Hosts in briefs"): "A private host already in the tree is
harvested (a promotion PR and its gate) before a second consumer is briefed against it", and
`policy.md`'s "do not write a third private variant": B contradicts both.

## Option A, built and checked (probes, not library changes)
- probe/KitProbe.lean: the eight privates copied verbatim into a module below `CodeSimulator`
  (renamed; `ic_input_suffix` kept private; the layout call restated over
  `pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`, its proof's `serializeK_eq` step
  replaced by `rw [unaryFin_eq]`; `serializeK` absent from the file, asserted). **With the
  report's six imports it fails** (probe/KitProbeSixImports.lean: 19 errors, `Unknown constant
  Turing.FinTM.pairExtractTM` …; `Build/Primitives` and `Build/StepBlock` are not in their
  closures). **With `Build/Primitives` and `Build/StepBlock` added it elaborates**: 0 errors,
  0 warnings; the seven public statements on the standard axioms.
- Cycle check: none of the eight imports' closures contains `CodeSimulator` or `NDCodeSimulator`
  (Primitives 15 modules, StepBlock 18, the six as in out/08; all eight are already upstream of
  `CodeSimulator` except UniversalStartup, InputWindow, SeamLayout — the overlay's imports).
- probe/KitProbeSealed.lean: the same, sealed over 22 other-file definitions (`prefixCanonTM`,
  `FinTM.pairExtractTM`, `pairEncode`, `pairDecode`, `embedSilentRetTM`, `embedSilentCfg`,
  `embedSilentTM`, `seamCompTM`, `seamReleaseTM`, `Cfg.mapState`, `MultiTapeTM.runFrom`,
  `MultiTapeTM.initCfg`, `MultiTapeTM.step`, `Cfg.init`, `Action.apply`, `Cfg.ofWords`,
  `stateWord`, `FinTM.bufferTape`, `StepBlock.summaryCells`, `tableBitsK`, `unaryFin`,
  `counterValue`) with `[-simp]` on `MultiTapeTM.initCfg`, `Cfg.init`, `Action.apply`: 0 errors.
  probe/KitSealControl.lean: 22 `rfl` controls, 0 errors unsealed, 22 errors sealed (one per
  goal). So the harvested proofs are rule-10 clean (the API-PR standard).
- probe/KitBridgeProbe.lean: from the restated `exists_layoutCall`, `ic_layout_call`'s
  original statement follows by `rw [serializeK_eq]; exact h M`, with `serializeK` sealed:
  equivalent.
- probe/NDCodeSimulatorRepoint.lean: `NDCodeSimulator` with the eight privates removed, the kit
  inserted as the published module would provide it, the uses renamed, and the layout call's
  one use adapted by `simp only [← serializeK_eq] at layouts`: elaborates with exactly the base's
  sorry warning (`exists_replayCanonizer`). The re-point is mechanical.
- Names: `prefixCanon_pairExtract_halt`, `embedSilentRetTM_firstReturn`, `headerCapture_run`,
  `seamCompTM_step`, `installCall_releasePhase`, `exists_windowCall`, `exists_layoutCall`,
  `embedSilentCfg_initCfg`, `Cfg.init_mapState`, `pairEncode_drop`, `InterpreterStartup`: unused
  at the tip, at both PR heads and on the 25 most recent local branches (`git grep -w`).
- Missing from the report's kit: U2-S's private `ss_captureInitial` (`UniversalK` 324–362), which
  B5a needs and the core did not (B5a's `S` starts from `S.tm.initCfg`; out/11).

## Size and replay closure of the API PR
- New module ≈ 330 lines for the eight (the probe's body) + 40 for the capture-initial identity
  + header/docstrings ≈ 400 lines; `NDCodeSimulator` −291 + 2 (the import and the `simp only`);
  the `TuringMachine` facade +1. About +405/−291.
- Replay closure (mkdownmulti.py; root excluded): the new module, `NDCodeSimulator`,
  `Diagonalization/NTimeHierarchy`, the `Diagonalization` and `TuringMachine` facades: **5
  modules** (re-pointing UN's `un_step` there too adds none). If `seamCompTM_step` goes into
  `Build/Seam` instead, Seam's closure is 88 modules — but the user's follow-up phase-host API PR
  (ruled 2026-10-24, `Build/Seam`, its own gate and replay) already pays that closure: the
  natural home at no extra replay.
- Interaction: the re-point changes `NDCodeSimulator`, C1's owned file in megafill C (one import
  line: C1's regions +1, its blob, its screen base). Either re-run C1's pre-ship at the new base,
  or leave the re-point to the dedup window (then the kit's public lemmas and the `ic_` privates
  coexist as a ledgered family until then).

## Re-check at #156's round-2 head `0e5f210b` (moved during the review)
The nine fingerprints hit the same files at `0e5f210b` as at the tip; the only new declarations in
`git diff 6e8db28f 0e5f210b -- TCSlib` are `phaseHostTM_tr_of_red_none` and `phaseHostTM_run_le`.
Every proposed name is still unused there and at the new tip `aad8a095`.
