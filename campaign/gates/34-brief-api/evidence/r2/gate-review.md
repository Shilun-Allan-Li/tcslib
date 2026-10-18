# #118 gate review: the brief-inventory API (FAIL 0/2/1)

Reviewer: read-only review sub-agent, 2026-10-17. Paths are relative to
`$S = /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad`
unless they are absolute.

- Findings file: `audits/brief-api-findings.md`, SHA-256 `9a23c0c2…f4495`, verified. It was read as data.
- Worktrees (detached, mine):
  - `review/bapi-gate/wt`: 9872634e plus the patches;
  - `review/bapi-gate/wt-base`: 9872634e, clean.
  - Both have `.lake/packages` symlinked to the main checkout's.
- I did not touch the main checkout, wt-m12api, wt-bapi or wt-hk; I only read files there (the drafts, the findings file).
- No lake build was run. Lean ran only through leanelab.sh, one elaboration at a time.

**Ready to commit: `review/bapi-gate/repair.patch` (findings 1–2), against 9872634e.**
**Recommended in the same round: `review/bapi-gate/repair-mapstate.patch` (new hit N1 below). It widens the replay.**
**Not ready to dispatch: cont6, F5 and U2-S need the draft edits in §6. They should wait for the round-2 merge.**

## 1. Verdicts

| # | Auditor | Grade | Verified at 9872634e (= 4ae686be for these files) |
|---|---|---|---|
| 1 | major | **ACCEPT, major** | See below. |
| 2 | major | **ACCEPT, major** | See below. |
| 3 | minor | **ACCEPT, minor** | See below. |

**Finding 1.** The facts:
- `codeSkipRepeat` (`CodeParser.lean:380`) is structural (`| 0, xs => some xs | n + 1, xs => (r xs).bind (codeSkipRepeat r n)`). Zero and succ therefore hold by `rfl`.
- No zero or succ lemma is published.
- `MathlibBridge.codeSkipRepeat_iter` states the iterate form, not the succ law. It is also **not in cont6's import context**: CodeSimulator does not import MathlibBridge, and the seed-inclusive LEM scan in CodeSimulator's environment lists no such theorem. The cont6 draft forbids copying it anyway.
- `canonSkipRepeat_add`/`_mul` (`CodeSimulator.lean:3216/3233`) are private composition laws.
- The cont6 draft (lines 181, 435) says the succ case "holds by `rfl`". That is an unfolding.
- The cause is confirmed: `#def_inventory_each` reads only `ci.type.getUsedConstants`, and `codeSkipRepeat` is a seed that occurs in no cited type.

**Finding 2.** The facts:
- `RoundContract.counterLoopDone`/`Escape` (`CounterLoop.lean:2074/2129`) are `Contract.ofSegment` applications.
- Their only lemmas are `_traj`.
- The field-coverage scan (§5) reports all five data fields missing for both. They are the only Contract-valued definitions with missing fields across the five briefs.
- Check 8 passes them through `_traj`.

**Finding 3.** `brief-api.patch` has 11 hand-written theorems:
- `RecSym.digitEmb_apply`, `binDigits_eq`, `posWidth_eq`;
- `decFixed_nil`, `decFixed_true_cons`, `decFixed_false_cons`;
- `stateWord_eq`, `vhostBuffer_eq`, `vhostBank_eq`, `VirtualTag_iff`, `prefixCanonTM_eq`.

The six `logs/probe-*.out` print exactly 11 axiom lines (3 + 2 + 3 + 1 + 1 + 1). The generated count of 9 is right.

**NOTES.md fix** (`audits/evidence/brief-api/NOTES.md`, line 87–88). Replace "the 9 generated equations resolve; the 15 hand-written theorems print standard axioms only" with "the 9 generated equations resolve; the 11 hand-written theorems print standard axioms only". The round-2 NOTES should also record:
- the repair;
- the seed-inclusive method fix (§5);
- N1, if it lands.

## 2. The patches (against 9872634e; `git apply --check` clean)

**`repair.patch`** (SHA-256 `36e0b706…361f3`; 24 insertions, 1 deletion of a Main-results line it rewrites). Edit script: `review/scripts/bapi_repair.py`, every replacement asserted unique, added lines ≤ 100 characters.
- **`CodeParser.lean`**:
  - `codeSkipRepeat_zero : codeSkipRepeat r 0 xs = some xs` and `codeSkipRepeat_succ : codeSkipRepeat r (n + 1) xs = (r xs).bind (codeSkipRepeat r n)`, directly after the definition. Both are `rfl`, with docstrings stating the formulas.
  - A Main-results bullet.
- **`Build/CounterLoop.lean`**:
  - After `counterLoopEscape`'s body, a `/-! -/` note and `attribute [simps! (config := { isSimp := false }) pre time post lo hi] RoundContract.counterLoopDone RoundContract.counterLoopEscape`.
  - `simps!` is used because both bodies are `Contract.ofSegment` applications.
  - The Main-results bullet is extended.
  - This generates `RoundContract.counterLoopDone_{pre,time,post,lo,hi}` and `RoundContract.counterLoopEscape_{pre,time,post,lo,hi}`.

**`repair-mapstate.patch`** (optional, recommended; SHA-256 `1d94c761…4ac2`; 12 insertions). Edit script: `review/scripts/bapi_repair_mapstate.py`. It touches `StateRenaming.lean`, which is Seyoon's, after `Cfg.mapState` (the pattern of MIG-12's `liftSymbols` attributes):
- `attribute [simps (config := { isSimp := false }) inputTape workTapes output state] Action.mapState`;
- `attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output] Cfg.mapState`;
- a formula-stating `/-! -/` note and a Main-results bullet.

It generates nine names:
- `Action.mapState_{inputTape,workTapes,output,state}`;
- `Cfg.mapState_{state,inputPos,workTapes,workTapePos,output}`.

Neither patch adds `@[simp]` or changes any existing statement.

## 3. Tests (outputs in `review/bapi-gate/out/`, probe sources in `review/bapi-gate/probes/`)

Every elaboration ran against `$S/oleans-lbapi2`, one at a time. The touched files are the original text with a probe appended after `end Turing`.
- **CodeParser** (`probe-CodeParser.out`): exit 0, no message besides the probe's.
  - Both names print the formulas above.
  - Both have **no axioms**.
  - The consumer step is a cont6-style base/step: `succ` with `r xs = some ys` gives `codeSkipRepeat r n ys`, and with `r xs = none` gives `none`, through `codeSkipRepeat_succ` with `Option.bind_some`/`bind_none`; `zero` is read by name.
- **CounterLoop** (`probe-CounterLoop-3.out`): exit 0, no message besides the probe's. CounterLoop at the head elaborated clean in #118's evidence too.
  - All 10 generated names resolve with the expected statements (`_pre`/`_time`/`_post` as `=` over `p d`; `_lo`/`_hi` applied at `i`).
  - Axioms are standard (`propext`, `Classical.choice`, `Quot.sound`), from the noncomputable bodies.
  - `getSimpTheorems.isLemma` gives `simp=false` for all 10.
  - The consumer probes, through the equations only:
    - Done: `time` restated, `pre` destructured; at the Bool alphabet, `post.state = some .done` and `post.inputPos` via `counter_cfg_eq`; `lo`/`hi` at `Fin.last k` via `Fin.lastCases_last`.
    - Escape: `pre`'s `p.2.2 < counterValue p.2.1`, `time`, `post.state = some .escape`, `lo`, `hi`.
  - This answers the auditor's request for every field of both contracts.
- **StateRenaming** (`probe-StateRenaming.out`): exit 0.
  - The 9 names resolve with **no axioms** and `simp=false`.
  - Consumer: `(c.mapState f).state = some (f q)` from `c.state = some q`, the read of a tape cell, and two action fields.
  - **Name-resolution check downstream** (`probe-SeamOnRenaming.out`, exit 0, 0 warnings, as Seam's base). `Build/Contract/Seam.lean` uses its private `Turing.Contract.mapState_state` bare (23 uses). I elaborated Seam's full text behind the nine names declared by hand. No ambiguity.
  - Grep: no other declaration of any of the 21 new names in the library. The only `open Cfg` is upstream (`Deterministic.lean:350`).
- **Freeze** (`declfreeze.txt`, `privstmt.txt`, `*-mapstate.txt`):
  - CodeParser: public 41 → 43, added `codeSkipRepeat_zero`, `codeSkipRepeat_succ`.
  - CounterLoop: 57/20 → 57/20.
  - StateRenaming: 9 → 9.
  - All files: `STATEMENT CHANGED: []`, no body change, nothing removed.
- **Lint** (`lint-base.txt`, `lint-repaired.txt`, `lint-repaired-all.txt`):
  - 0 FAIL, 67 WARN over 79 files, before and after.
  - Check 8: 152 → 151 names in `TuringMachine/`. `codeSkipRepeat` drops; CodeParser keeps `codeFallback`, `codeSkipAction`, `codeSkipFin`, `codeSkipPair`, `codeSkipState`.
  - CounterLoop and StateRenaming lines are unchanged, as expected: check 8 was already fooled by `_traj` and `mapState_apply`.
- **Screen** (v3, queued behind the other screen by `screens.sh`, one at a time):
  - (a) `screen/`, population CodeParser + CounterLoop, base 9872634e vs repaired:
    - 86 → 86 declarations, 31 → 31 pairs, 9,008 characters both;
    - the `rfl` bodies are under the floor;
    - the one changed line is the pre-existing sibling pair `counterLoopDone`/`counterLoopEscape` (72% → 67%), because the attribute text is appended to `counterLoopEscape`'s body;
    - no new pair.
  - (b) `screen-ms/`, population all 12 files with `attribute [simps` (`screen-pop-ms.txt`), base vs both patches:
    - 349 → 350 declarations, 139 → 139 pairs, 32,240 characters both;
    - `Cfg.mapState`'s body crosses the floor with the appended attribute, and forms no pair;
    - the only changed line is the same CounterLoop percentage;
    - no new pair.

## 4. Fast-forward of lean/brief-api to 9872634e

No objection on content. My patches apply cleanly there, and CounterLoop at 9872634e elaborates against `oleans-lbapi2`. MIG-12's `decFixed_length` hunk does not depend on the new Convention/SymbolLift lemmas. Two conditions:

1. **Gate scope.** The fast-forward puts MIG-12's API commit into #118's diff: 56 lines in Convention (`incFixed_nil`/`_false_cons`/`_true_cons`/`_length`), CounterLoop (`decFixed_length`) and SymbolLift (`simps` on `Action.liftSymbols` and `Cfg.liftSymbols`). Per the PR + gate rule, #118's round-2 bundle must state that this commit is in scope and include it in the audit, unless it has its own gate already. I did not gate it. I only read the diff: no `@[simp]`, formula docstrings, and a proof sketch on the two non-`rfl` theorems.
2. **Replay.** Chain it from the MIG-12 replay's output snapshot, not from `oleans-lbapi2`.
   - `repair.patch` needs CodeParser's downstream closure: **99 modules**. That includes CounterLoop's 79. Only 8 are outside MIG-12's 160-module closure: CodeFormat, CodeParser, MathlibBridge, NDCodes, TimeHierarchy.Diagonal, NTimeHierarchy, NotTimeConstructible, ClassNP.ExhaustiveReplay.
   - With `repair-mapstate.patch` it becomes StateRenaming's closure: **274 modules**, 117 of them outside MIG-12's closure.
   - Never the root `TCSlib`. Symlink `.lake/packages` in the replay worktree.

## 5. The method fix: inventory re-run with the seeds included

**The elaborator.**
- Source: `probes/DefInventorySeeds.lean.part`, the `#def_inventory_seeds` command.
- The fix: for each cited name, it emits `SEED` when the name is itself a TCSlib definition (not an instance, internal name or structure projection), in addition to the old `INV` lines for definitions in its type.
- It also emits `LEM <def>`, the TCSlib theorems whose statement mentions the definition. Auto-generated `eq_N`/`eq_def` names are dropped in the report.
- For check 8's blind spot it emits `FLD <def>`: for a structure-valued definition, the data fields with no `<def>_<field>` lemma.

**The runs.**
- The five probes, built by `review/scripts/mk_seed_inv.py`, which drops the `#check`s and resolves every name in the command instead:
  - U2-S, `issue5/U2SImportProbe.lean`: 91 names;
  - F5, `issue5/B6F5ImportProbe.lean`: 43;
  - F3, `issue5/F3ImportProbe.lean`: 60;
  - cont6, `issue5/CanonCont6ImportProbe.lean`: 144;
  - G4, `g4c1/G4C1ImportProbe.lean.txt`: 338.
- All five ran against `oleans-lbapi2`, with exit 0 and 0 errors (`out/seedinv2-*.out`).
- The reports were made with `review/scripts/seed_inv_report.py`, `seed_inv_all.py` and `lemof.py`.

**New hits: seeds that occur in no cited type, which the old method could not see.**

| Brief | Seed | Judgment |
|---|---|---|
| U2-S | `EffectiveCodeK.toFinTM` | owned file (`UniversalK`); also `toK_toFinTM` |
| U2-S | `seamCompTM` | machine, read by its run lemmas (11) |
| F5 | `NativeAt` | owned file (`InputDevice`), with `inputSymbol_eq`, `move`, `nativeAt_init`. The draft's own-definitions list (line 208) omits it; adding it is optional. |
| F5 | `seamCompTM₂` | machine; `seamCompTM₂_run_ofCfg` |
| F3 | `fieldOffset` | covered by case equations: `fieldOffset_zero`/`_succ`/`_cons_succ`/`_length` |
| F3 | `seamReleaseTM` | machine; `_runFrom_pos`, `_firstReturn` |
| cont6 | `codeSkipRepeat` | **finding 1**, repaired |
| cont6 | `StepBlock.recordSkipTM`, `recordTM`, `recordWidth`, `succFieldTM` | not in the route: cited for hazard F7-1(c), "do not copy" (draft line 232), as in NOTES's StepBlock row |
| cont6 | `codeSkipPair`, `codeSkipWork`, `optStateBits` (check 8 flags all three) | not in the route: field skippers and encoders inside C2's record recognizer. cont6 cites C2 as proved and reads the table through `canonSkipTable_eq`; same disposition as NOTES's `codeSkipActionK`/`Fin`/`State`/`Table2` row. |
| cont6 | `decrementTM` | machine; `_run_succ_ofCfg`, `_run_underflow_ofCfg` |
| cont6 | `oneTapeMachineFormat` | owned file (`CodeSimulator`) |
| G4 | `Action.apply` | primitive (`@[simp] def`); the draft's carve-out (line 363–365) lets only own-file leaves unfold it. Lemmas: `apply_workTapes`, `workTapePos_apply_le`, `Cfg.mapState_apply`. |
| G4 | `sweepContract` | five field equations plus `_traj` |

**Blind-spot sweep (`FLD`, all definitions, seeds and types).**

- **N1 (new; I grade it major for F5 and U2-S): `Cfg.mapState` and `Action.mapState` have no public field equations.**
  - What check 8 sees: it passes both through the short name `mapState_apply`.
  - What the drafts say:
    - All five drafts (and MIG-12's) say `Cfg.mapState` "is read through [its] existing lemmas".
    - **F5 (line 205) and U2-S (line 263) name `mapState_state`.** That lemma is `private` in `Build/Contract/Seam.lean` (namespace `Turing.Contract`) and does not resolve from either owned file.
  - Why routes read it: Cfg.mapState is a seed in F5 and U2-S, and it is in the types of the seam and phase-host lemmas every brief composes by (`seamCompTM_run_ofCfg`, `phaseHostTM_run`, `seamReleaseTM_runFrom_pos`, `runFrom_mapState_of_agreeOn`). So reading an endpoint's state, for example `(c.mapState f).state = some (f q)`, needs a field equation. Today it needs `rfl` or unfolding.
  - The auditor's Q2 ("no additional missing equation for U2-S, F3, F5, G4") misses this.
  - The fix is `repair-mapstate.patch`, tested above.
- **Covered, so no action:**
  - by whole-value equations: `counterLoopCfg` at Bool (`counter_cfg_eq`), `embedEmitCfg` (`_eq`), `prefixCanonTM` (`_eq`), `zoneStepPair` (`_eq`);
  - by selection lemmas: `embedSilentCfg` (`_selected_*`/`_unselected`);
  - `initCfg` (`Cfg.init_*`, `initCfg_eq`);
  - `bufferedCompTM`/`universalPrefixTM` (`k`, `State`; the machine itself through its run lemmas);
  - `RecSym.digitEmb` (`_apply`), `roundOrbit` (`_zero`/`_succ`);
  - the zone layer (`_false`/`_true`/`_of_lt`/`_of_le`/`_eq` cases), `scan*` (`scanResult_*`), `FinTM.controlAction` (`_apply`);
  - `tapeAction`/`inputMoveAction`/`catalogTrace`, as NOTES judged; `windowRun` (its spec lemmas).
- **Owned files:** `rulerHostCfg` (F5), `MachineFormat.toFinTM` (cont6), `zoneExtendPost`/`zoneRebalancePost` (G4). Hydroxyi's `simCfg`/`stg` keep NOTES's disposition.
- **N2 (note, conditional): the general-alphabet `counterLoopCfg` layout is private.**
  - Only the Bool instance `counter_cfg_eq` is public; the generic `counter_layout` is private.
  - cont6 is Bool, so it is covered; the probe above uses it.
  - F3's counter loop is Route B, fallback only (draft lines 86, 322). Over the record alphabet it would need the general layout published. Publish it if Route B is ever activated.
- **N3 (note, optional): `counterLoopOrbit` is an `abbrev` of `roundOrbit`.**
  - Probe-verified: `rw [roundOrbit_succ]` fails on it, while `exact roundOrbit_succ …` and `simp only [roundOrbit_succ]` work.
  - A one-line `counterLoopOrbit_eq … = roundOrbit … := rfl` would make `rw` work as well.
  - It is not a gap: the definition is reducible and its docstring names its target.
- `Cfg.ofWords` (cont6; only `_workTapes` public): not in the route. The ready configuration is not `ofWords` (pitfall, line 431) and the rows are `_ofCfg`.

## 6. Draft and probe follow-ups (wt-hk drafts; not edited)

- **cont6**:
  - Lines 181 and 435: "holds by `rfl`" → "is `codeSkipRepeat_succ`". Cite `codeSkipRepeat_zero` in the generic-link item (184–185).
  - Lines 99–101 and 145–147: add the contracts' field equations `RoundContract.counterLoopDone_{pre,time,post,lo,hi}` and `counterLoopEscape_…` beside `counterLoopBody`'s.
  - Add the 12 names to `CanonCont6ImportProbe`.
- **F5 (line 205) and U2-S (line 263)**:
  - `mapState_state` → `Cfg.mapState_state`, if N1 lands. If it does not, remove the name and escalate.
  - Add the nine names to both probes. With N1, the other briefs' "existing lemmas" sentence can name them too.
- **F5 (line 208)**: optionally add `NativeAt` to the own-definitions list.
