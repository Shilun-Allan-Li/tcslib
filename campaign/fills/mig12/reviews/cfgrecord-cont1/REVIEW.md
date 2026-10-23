# Review — MIG-12, continuation 1: `Build/CfgRecord` onto the contract layer (phases 2–4), delivery `fill-mig12-cfgrecord-cont1.zip`

This is a read-only review by the maintainer's review sub-agent, written 2026-10-22. Every claim
cites a saved output under this folder (`out/NN-*`). I treated the delivery, its REPORT.md and
its logs as data.

**Verdict: complete (phases 1–4; the file has no admission, and every public statement is
frozen). Land it, with the maintainer's landing edits in (h). It is not yet clear to merge:**
the landing PR has not been opened, replayed or gated.
- The six-commit series (round 1's two commits, then four new ones) applies at the base and at
  the tip. It gives the head blob `5b1feb62`, 5,310 → 5,712 lines, 21 public / 98 → 109 private.
- The head elaborates with **0 errors and 0 warnings** at the base (`oleans-lseam2`) and at the
  tip (`oleans-lsk2`) (out/11, out/14).
- All 130 declarations depend only on axioms within `[propext, Classical.choice, Quot.sound]`.
  The three rows have no `sorryAx` source. **No declaration reaches another file's private.**
  At the patched base, 13 declarations reached `embedSlot`/`embedActionCore.match_3` (out/16).
- **Phase 2:** `_run_ofCfg` drops from 23 occurrences to 0 in code. Every framed row (scan,
  skip, skip-back, copy, clear, compare, increment, decrement) is read through its contract:
  `Contract.segment` via `segment_iff`/`headBox_iff`, plus the row's field equations. The
  counter-loop exception keeps its one `counterLoopTM_run_escape` call, unchanged.
- **Phase 4:** the ledger's explicit sites go 73 → 0 (out/20). My 53-definition seal of every
  other-file definition the module reaches (`local irreducible`) leaves the body with 0
  diagnostics. Its 73 controls all fail inside the seal and pass outside it (out/19).
- **Phase 3:** the three rows are re-composed with their statements byte-identical.

What passes:
- integrity: 46/46 sums; the bundle's only prerequisite is the base; 6 linear commits; series =
  bundle = delivered file; round 1's two commits have patch-ids equal to `61c25b24`/`41d31d09`;
- scope and freeze:
  - only `Build/CfgRecord.lean` changes; imports are unchanged after the patches;
  - all 21 public docstrings and statements are byte-identical;
  - 11 privates added, 0 removed, 33 changed; one private statement changed (`R` → `_R`);
  - no new public declaration;
- the axiom and admission walks;
- rule 10: seal S1 is clean, with controls; no other-file definition among the 195 identifiers
  in the `rw`/`simp` lists of the added code;
- rule 11;
- the brief's 227-check probe: standalone at the base and at the tip, and in-module. 0 errors
  each. The worker's log is byte-equal to mine;
- the v3 screen: byte-equal to the worker's. 870 → 879 declarations, 435 → 440 pairs; 6 new
  directed pairs, all in-file and below 90%; no cross-file pair;
- lint: 0 FAIL / 30 WARN, as at the patched base. No line over 100 characters was added;
- the worker's 280-module final sweep: 280/280 exit 0, 0 errors, 83 sorry warnings equal by
  name to the base set, `CfgRecord` with no diagnostic.

Findings (none blocks landing):
- **F1 (route and size; decision D4).** The swap reads every row through its contract. It then
  converts the segment straight back into the old run theorem's shape and keeps every scalar
  proof.
  - `recordStep_contract_clauses(_range)` turns `C.segment` back into the three scalar clauses
    `X_run_ofCfg` used to return: the run equation, the cut and the per-tape `Icc` envelope.
  - About 67 added lines turn the contract's `Icc p p` envelope of an untouched tape back into
    an equality (`le_antisymm`, if-splits of `lo`/`hi`) to feed the unchanged proofs.
  - The brief's recommended form keeps the `Segment` and weakens it with `Segment.mono` and
    `record_headBox_mono`. It is not used beyond phase 1.
  - The result is **+402 lines (5,310 → 5,712)**, against the design estimate of −1.6k to −2.1k
    for the migration.
  - REPORT reports the delta. Its explanation is wrong: "the compression the estimate
    anticipated was in the retired `RecordRun` kit (phase 1, already in the patches' figures)".
    Phase 1 was +8 lines (round 1's review).
  - The gate's fidelity criteria are met: contracts read through their fields, no hand trace,
    no unfolding by the brief's measure.
- **F2 (rule 10, minor, existed before this delivery; decision D2).** `recordStep_cell_write` is
  unchanged since the base. It closes its two `simp [recordStepWriteCell, …]` goals only
  because `Turing.Action.apply` is `@[simp]`.
  - With `attribute [-simp] Turing.Action.apply Turing.Cfg.init` added to the seal (S2), it is
    the only failing declaration (out/19).
  - The ledger did not list it, and the worker's seal could not see it: `local irreducible`
    does not block simp's equation lemmas.
  - So REPORT's "every per-definition count 0" holds under the brief's measure, but not under
    simp erasure.
  - A re-proof through `Turing.Action.apply_workTapes` (+3 lines, `probes/cell-write-fix.diff`)
    elaborates with no output, and S2 is then clean.
- **F3 (frozen docstrings; landing edits, decision D3).** Five passages in frozen public
  docstrings describe routes the proofs no longer take:
  - round 1's M2: `RecordRun` twice in `exists_recordStepTM` (lines 4682, 4700), and
    `recordRun_trans` in `exists_recordEqTM` (4946);
  - new with this delivery: `exists_recordEqTM`'s sketch cites `compareTM_run_ofCfg` (4938),
    but the proof uses `compareTM_contract` with its exact time;
  - new with this delivery: `Cfg.inWindow_init`'s "**Proof sketch.** Unfold `Turing.Cfg.init`."
    (5706), but the proof now reads `Cfg.init_workTapePos`/`_workTapes`.

  The module's status text also needs the maintainer's update. The texts are in (h).
- **F4 (public-facing text, cosmetic).**
  - New or rewritten private docstrings use review vocabulary: "the public R1 reconstruction
    lemma" (`recordStep_restrict`), "the public scan contract", "the public clear contract".
  - `recordStep_fieldOffset_congr` (23 lines with its statement) has no literal "Proof sketch".
  - No campaign label, path or date was added (out/28). Optional rewordings are in (h).
- **F5 (records, minor).** REPORT is accurate in substance. Ten details:
  1. **The worker's seal is not checkable from the delivery.** Its source is not shipped, the
     final logs `seal-all6.log` and `seal-all7.log` are empty (0 bytes), and there is no
     control. My seal replaces it.
  2. The log cited for the module's 0/0 result, `check-groupJ.log`, is empty. The real
     evidence is the final sweep's `CHECK 158/280` with no diagnostic, plus my elaborations.
  3. "Ten need none": **5** of the 32 printed declarations need no axiom. The worker's 32 prints
     equal mine.
  4. "Long lines: 151": the patched base has 110 lines over 100 characters (158 by bytes) and
     the head 95 (143). "No new line over 100" holds.
  5. REPORT's phase-2 list omits `recordStep_arithmetic_transport`, which now reads
     `incrementTM_contract`/`decrementTM_contract`.
  6. Environment records:
     - no package-verification log is shipped (the clone lines of `cache-get.log` match the
       manifest);
     - `cache-probe.log` is empty;
     - the zero-size-olean check is not logged;
     - the checkpoint zips cp1 and cp2 are not in the inbox.
  7. The bundle's only ref is `HEAD`, not a branch.
  8. Commit identities are mixed: "Codex" (round 1's two commits), "Fill Agent
     <ragavanbsco@mit.edu>" (the user's own address; commits 3–4) and "Claude
     <noreply@anthropic.com>" (commits 5–6). Decision D5.
  9. The remaining bootstrap (19:37–20:06Z) overlapped the last edits and checks of the owned
     file. A check of the owned file pruned its olean at 19:47, so `Build/RecordTable` failed
     once and was retried. The brief asks for one Lean process at a time for this file.
     Nothing went wrong (15.3 GiB headroom, no exit 137). The final sweep ran after the last
     commit and is clean.
  10. REPORT's ledger table covers exactly the 173 rows (76 explicit, 97 implicit) (out/32).
- **N1 (duplication).** The swap adds pairs (+6 / −1 directed, all in-file), where the brief
  says "a swap should remove pairs, not add them". All are below 90% and justified in REPORT.
  The top one, 84%, is the two contract readers; a single reader over an arbitrary exit set
  would remove it.
- **N2 (public constants, workflow §4).** The new public constants are compiler auxiliaries
  only: `Turing.copyTM_contract.congr_simp` and `Turing.compareTM_contract.congr_simp`
  (generated here by `simp`), and `exists_recordEqTM._proof_1_74`, a renumbered auxiliary.
  `counterLoopOrbit.eq_1` and `_proof_1_51` are gone. None is a public declaration. The 280-module
  sweep imports the module beside every other consumer of the two contracts without a clash
  (out/34).

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-mig12-cfgrecord-cont1.zip` | SHA-256 `0e29da88…5fe23c6`, 249,636 B, 50 entries. Copied to `delivery/` and extracted there: no unsafe path, no symlink, CRC OK, every member byte-equal, no extra file. No C file, no script | out/01 |
| `SHA256SUMS` | 46/46 OK; covers every member except itself | out/02 |
| Brief, dispatch copy `exchange/outbox/fills/mig12-fill-cfgrecord-cont1.md` | `0ee25ec5…01a92bc5` (as given). It equals the repository copy `campaign/fills/mig12/briefs/` (`6e47ae8a…`, the same at the base, at `9f8bba86` and at the tip) with its three `@ANCESTOR@` set to the base. REPORT quotes the same hash | out/03 |
| Addendum | v2.4 = `9f8bba86`'s `42555a4f…f1d0`, the hash REPORT quotes. The base carries v2 (`2a80b0ef…`), the tip v2.5 (`90851511…`, ignored) | out/03 |
| Base | `96d60278e4fde29b986ec1d0e59cd07f768fe28a`, a records commit; its TCSlib sources are `dac6b3b0`'s (no `.lean` under `TCSlib/` differs) | out/13 |
| Head | `8b0b0bf4b7e97b4dbb611d91b67fe2b2b248dc34`, fetched from the bundle into a scratch bare clone `git/` (shared objects, read-only on the main repository) as `refs/review/mig12-cont1` | out/04, out/05 |
| Round 1 | `61c25b24` (import), `41d31d09` (the `Segment` swap), head blob `1c9d198f`; the brief's input patches `0001`/`0002` (`b6d69f6d…`, `98fba4bb…`) | out/06 |
| Snapshots | `oleans-lseam2` (the base tree; the pre-ship ran against it). `oleans-lsk2` (`0416ffea`'s tree). `CfgRecord`'s 28-module upstream closure has the same blobs at `0416ffea` and at the tip `144201de`; from the base to the tip, only `TuringMachine/Simulation` changed (#132, +23 lines) | out/13 |
| Campaign tip | `144201de` (#145, #146, #148 merged). Open Lean PRs: **#147** (`lean/u2s-startup-cont1` @`28150fc1`: `UniversalK`, the facade) and **#149** (`lean/spaceused-api` @`097f3e04`: `Deterministic`, `Finite`; additions only, no attribute) | out/35, out/35b |

Review worktrees, all detached under this folder; I checked for `.lake/packages` before linking
it:
- `wt-pbase`: the base with the brief's two patches, by `git apply`, uncommitted;
- `wt-head`: the base with the delivered series 0001–0006, by `git apply`;
- `wt-tip`: `144201de` with the series.

Constraints observed:
- Lean ran only through `tools/leanelab.sh`, one elaboration at a time.
- The screen ran once, niced, holding `locks/screen.lock`.
- No build or cache command was run; nothing was compiled or run from the zip.
- Python ran under `-I`, with scripts in `scripts/`.

I read the whole diff (out/09, 1,978 lines). The generated Lean files are in
`wt-*/ReviewScratch/`; small ones are copied in `probes/`. Hashes of every script and probe are
in out/37.

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Zip, sums | PASS (above) | out/01, out/02 |
| 2 | Bundle | PASS: `verify` okay; requires only `96d60278…`; one ref `HEAD` = `8b0b0bf4…` (F5.7) | out/04 |
| 3 | Commits | 6, linear, each touching only `Build/CfgRecord.lean`: <br>• `5d02122a` +1 (the import); <br>• `e1ff1a57` +197/−190 (phase 1); <br>• `4a756f0b` +182/−36, `8f90ee27` +122/−57 (phase 2/3); <br>• `90410caa` +357/−174 (phase 4); <br>• `8b0b0bf4` +16/−8 (wraps). <br>Patched base → head: +665/−263 | out/05, out/06 |
| 4 | Round 1's patches | PASS: `5d02122a`/`e1ff1a57` have the patch-ids of `61c25b24`/`41d31d09` and of the input patches (`06b4d3d5…`, `f2b9c71e…`); the blob after them is `1c9d198f` (5,310 lines). The delivered 0001/0002 differ from the inputs only in `From`, `n/6` and the git-version line | out/06, out/07 |
| 5 | Series = bundle = file | PASS: 0001–0006 apply at the base; the result is blob `5b1feb62`, the bundle head's blob and the delivered `CfgRecord.lean` (SHA-256 `6c5cae70…d824`). Each patch equals `format-patch --full-index` of its commit, except the abbreviated index and the git-version line | out/07, out/08 |
| 6 | Freeze (`declfreeze.py`, comment-aware; publics authorized for body changes) | PASS: 21 → 21 public, none added or removed, no `STATEMENT CHANGED`. Body changes only in the three rows and `Cfg.inWindow_init` | out/10 |
| 7 | Publics byte for byte | PASS: docstring + statement of all 21 `frozen-publics.txt` names identical, patched base → head and base → head. The other 17 publics are wholly unchanged | out/10 |
| 8 | Privates (`declfreeze`, `privstmt`, `swapstmt2`) | 98 → 109: 11 added, 0 removed, 33 changed. One private statement changed: `recordStep_restrict`'s unused machine argument `R` → `_R` | out/10 |
| 9 | Imports, header | PASS: the five imports are unchanged after the patches; lines 1–427 (header, layout facts, `RecordSeg` kit) are identical | out/10 |
| 10 | Hygiene (664 added lines) | no `sorry`, `admit`, `axiom`, `set_option`, `open`, `section`/`namespace`/`end`, `variable`, `attribute`, `instance`, `native_decide`, `unfold`, `delta` or `#` command. The 5 `decide` are terms or `by decide` on `Fin` disequalities. The 2 `change`s, 13 `show`s and 43 `rfl`s are covered by the seal (row 22). Maximum width 98 | out/10, out/27 |
| 11 | Size | 5,302 (base) → 5,310 (patched) → **5,712**; 21 public / 109 private (lint INFO) | out/26 |
| 12 | Elaboration, head at the base (`oleans-lseam2`) | PASS: exit 0, **no output**; 24 s, 2.54 GB peak. Patched base: the same. A copy with a planted false `rfl` reports its error | out/11, out/11b, out/12 |
| 13 | Elaboration at the tip (`wt-tip`, `oleans-lsk2`) | PASS: exit 0, no output; 25 s | out/14 |
| 14 | Axioms (in-module copy: `#print axioms` for all 130 declarations) | PASS: histogram 67 `[propext, Classical.choice, Quot.sound]`, 23 `[propext, Quot.sound]`, 7 `[propext]`, 4 `[Quot.sound]`, 29 none. Equal to the worker's 32 prints on every name | out/16 |
| 15 | Admission walk | PASS: `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM`: direct `sorryAx` users in their closures `[]` | out/16 |
| 16 | Other files' privates, equation lemmas | PASS. At the head, no declaration reaches an external private. At the patched base, 13 reached `Build/Embed`'s `embedSlot` and `embedActionCore.match_3`, and the rows also reached `MultiTapeTM.step.eq_1`, `outputSymbol.eq_1`, `roundOrbit.eq_1` and `counterLoopOrbit.eq_1`. At the head the only hits are `Action.apply.match_1`: by `simp` in `recordStep_cell_write` (F2), elsewhere by matcher reuse (S2 clean), plus the tool's known `Bool.eq_*` false positives | out/16, out/16b |
| 17 | New public constants (workflow §4) | auxiliaries only (N2) | out/34 |

**The 11 new privates** (head lines):
- the contract readers `recordStep_contract_clauses` (435) and `…_range` (449);
- the record-literal forms `recordStep_sweepPost_eq` (463) and `recordStep_seekPost_eq` (482),
  from the published `sweepPost_*`/`seekPost_*`;
- the renaming kit `recordStep_mapState_eq` (497), `recordStep_mapState_mk` (513) and
  `recordStep_mapState_snapshot` (1814), through `Cfg.mapState_*`;
- `recordStep_runFrom_one` (520) and `recordStep_orbit_one_step` (526), from `runFrom_succ_eq_step'`
  and `runFrom_zero`, and `roundOrbit_succ`;
- `recordStep_fieldOffset_congr` (536), from `fieldOffset_zero`/`fieldOffset_cons_succ`; it
  replaces the ledger's one `unfold fieldOffset` and a local induction;
- `recordStep_embed_update` (734), the embed-and-update record equality through
  `embedEmitCfg_eq` and `Cfg.liftSymbols_*`; it carries `recordStep_restrict` and
  `recordStep_seek_transport`.

REPORT's list matches, name for name.

## (b) The brief's targets

| Target | Status | Notes |
|---|---|---|
| Phase 1 (the two patches) | **as briefed** | applied first, by patch-id; `RecordSeg` stated once, its readers kept |
| Phase 2: phase lemmas over the row contracts, never by destructuring a run theorem | **done** (F1 on the form) | `_run_ofCfg` 23 → 0 occurrences in code (the one left is in `exists_recordEqTM`'s frozen docstring, F3). Rows read: `scanTM_contract` (scan, map, fold, the tape scans), `skipTM_contract`, `skipBackTM_contract`, `copyTM_contract`, `clearTM_contract`, `compareTM_contract` (exact time `2·compareStop + 2`; the old existential bound by `compareStop_le`), `incrementTM_contract` and `decrementTM_contract` (in `recordStep_arithmetic_transport`, indexed by `(w, v)`). Each is read through `Contract.segment` (`segment_iff`, `headBox_iff`) plus `X_contract_pre/time/post/lo/hi`. No contract is destructured by its fields' definitions (seal row 22) |
| Inside the host | **as briefed** | `recordStep_phase_run` keeps one `phaseHostTM_run` per phase, the brief's second option. `Cfg.mapState` is read through `Cfg.mapState_*` (the new renaming kit). The host's verdicts are excluded by stage index (`record_tag_ne`, `recordStep_tagged_segment`, unchanged) |
| Counter-loop exception | **as briefed** | `recordStep_save_run` keeps its one direct `counterLoopTM_run_escape` (head 1048); the declaration is unchanged. No counter-loop contract was written |
| Sequences | **as briefed** | `Segment.trans` throughout; no `Contract.seq` |
| Phase 4: the ledger's 173 rows | **done** | explicit 73 → 0 (the ledger's 21 names; base 76 → patched 73, as in round 1). Definitional: seal S1 clean. The `embedEmitCfg` rows are re-pointed (`embedEmitCfg_eq`, `_selected_*`, `_state`/`_inputPos`/`_output`), so the `Build/Embed` privates are gone (row 16). `counterLoopOrbit`'s rows go through `show … from roundOrbit_zero/recordStep_orbit_one_step` ascriptions, the brief's "through the abbreviation". One site outside the ledger remains (F2) |
| Phase 3: the three rows | **done** | statements frozen. `exists_recordEqTM` uses the compare contract's exact time and `recordStep_fieldOffset_congr`; `exists_recordStepTM` uses the congruence and the cell-word equation generalized over the configuration. Line delta reported (F1) |
| No public declaration, imports, rule 7 | **as briefed** | no second segment layer, host, seam, embedding transport or row trace. The two readers are thin wrappers of `segment_iff` |
| Escalations | none raised; I agree | every fact is read from a published equation; the probe and the citations resolve (rows 26–28) |

**What REPORT claims, checked:** STATUS COMPLETE, 0/0, the freeze, 98 → 109 privates, the
explicit 73 → 0, "per-definition counts 0" (true under `local irreducible`; F2), the probe, the
axioms (F5.3), the walks, lint (F5.4), the sweep, and the screen. All hold, except the details
in F1, F2 and F5.

## (c) Rule 10 and rule 11

| # | Check | Result | Evidence |
|---|---|---|---|
| 18 | Seal set | **53 definitions**: every semireducible, non-projection, non-instance, non-matcher TCSlib definition reached from the module's 130 declarations at the head or at the patched base (`#kinds` over the 252 reached constants). It contains the ledger's 20 sealable definitions. `counterLoopOrbit` is a reducible abbreviation. `Action.apply` and `Cfg.init` are the only `@[simp]` ones | out/17, out/18 |
| 19 | Controls | for each sealed definition, `#rfl_control`: `rfl` on `c = <c's own body>` at default transparency. **Unsealed: all 51 close, plus 2 closed-instance `rfl`s and 2 `simp` controls, 0 errors. Sealed: all 55 fail.** For `decFixed`/`incFixed` the generic control never closes (smart unfolding on a variable), so a closed instance replaces it (`decFixed [true] = some [false] := rfl`, `incFixed [false] = some [true] := rfl`) | out/19-seal/M12C1ControlUnsealed.out, …Sealed.out |
| 20 | **S1**: the whole module with `attribute [local irreducible]` on the 53, after both `namespace Turing`; 55 controls at the top, 20 (the ledger's) at the end | **body: 0 errors, 0 warnings**; exactly 73 errors, the controls | out/19-seal/M12C1SealS1.out, out/19-seal-summary.txt |
| 21 | **S2**: S1 plus `attribute [-simp] Turing.Action.apply Turing.Cfg.init` in both namespace blocks | body: **only `recordStep_cell_write`** (2 unsolved goals, 3 unused-simp-argument warnings; F2). All 77 controls fail. With the proposed re-proof: exactly the 77 controls, 0 warnings; unsealed it elaborates with no output | out/19-seal/M12C1SealS2*.out, `probes/cell-write-fix.diff` |
| 22 | Power at the base: S1 on the patched base | 48 body errors in 19 declarations before Lean's 100-error cap (`recordStep_save_transport` 6, `recordStep_restrict` 6, `recordStep_arithmetic_transport` 5, …) | out/19b |
| 23 | `rw`/`rwa`/`simp`/`simpa`/`dsimp`/`simp_all`/`unfold` arguments touching added lines | 315 lists, 643 occurrences, **195 identifiers, each resolved in-module**: <br>• 88 TCSlib **theorems** (`X_contract_*`, `sweepPost_*`, `seekPost_*`, `Cfg.mapState_*`, `Cfg.liftSymbols_*`, `embedEmitCfg_*`, `Action.apply_*`, `MultiTapeTM.step_of_some`/`outputSymbol_of_some`/`runFrom_zero`, `FinTM.bufferTape_eq`/`_left`, `fieldOffset_*`, `decFixed_*`/`incFixed_*`, `counterWord_*`, `roundOrbit_succ`, `Cfg.init_*`, `Cfg.inputSymbol_of_*`, `Cfg.workTapeSymbols_eq`, `decodeBool_apply`); <br>• 13 of this file's own; <br>• 65 locals; <br>• 28 core/Mathlib theorems and one core definition (`Functor.map`, existing text moved into `cellWord`). <br>**No other-file TCSlib definition.** The 15 `show`/`change` lines restate goals through projections of explicit records, `let`s, this file's `cfgRecord`, or the abbreviation; S1 covers them | out/21-rwargs-summary.txt, out/21b |
| 24 | Rule 11 | PASS: none of the six R3 rows occurs in the file (code or comments) or among the 234 TCSlib constants reached. No `_run_ofCfg` is reached, no `_private` token occurs, no external private is reached (row 16) | out/22 |

## (d) Probes, citations, promotion candidates

| # | Probe | Result | Evidence |
|---|---|---|---|
| 25 | Brief's `MIG12ImportProbe.lean.txt` (blob `504e6e26`, the base's), standalone against `oleans-lseam2` | 227 outputs, 0 errors, 0 warnings. **Byte-equal to the worker's `import-probe.log`** | out/23-…-lseam2.out |
| 26 | The same, standalone at the tip (`wt-tip`, `oleans-lsk2`) | 227, 0 errors, 0 warnings | out/23-…-lsk2.out |
| 27 | The 227 checks appended to the delivered module | 227, 0 errors, 0 warnings | out/23-…InModule-lseam2.out |
| 28 | The worker's probe | none was written; REPORT re-ran the brief's (row 25). No probe of the new citations was made | — |
| 29 | Theorems cited by the 48 new or changed declarations outside the 227 | 30, all public at the base and at the tip (rows 12–13): the `runFrom`/`step` equations, `Cfg.ext`, `Cfg.init_*`, `FinTM.bufferTape_eq`, `FinTM.moveInputPos_neg_val`, `counterWord_zero`/`_length`/`_value`, `counter_cfg_eq`, `decodeBool_apply`, `exists_inputSeekTM`, `length_joinFields_add_one`, `roundOrbit_zero`/`_succ`, `seekPost_*`, `sweepPost_*`, `step_of_inputMoveAction`. Most are named by the brief's ledger table or were already cited in unchanged text | out/24 |

**Promotion candidates** (the maintainer's 12.2c window):
1. **A contract segment reader** (the two `recordStep_contract_clauses` lemmas, as one
   statement over an arbitrary exit set). This is the strongest candidate: every consumer that
   reads a contract with scalar clauses needs it, and it belongs in `Build/Contract/Basic`
   beside `segment_iff`. As one lemma it also removes N1's 84% pair.
2. **`MultiTapeTM.runFrom_one`** (here `recordStep_runFrom_one`) belongs in `Deterministic`,
   for any alphabet. It is also `Turing.runFrom_one` (`Build/EmitIterEmbed`, `Bool` only, by
   unfolding `runFrom`) and `xr_runFrom_one` (`ExhaustiveReplay`, private): three copies.
3. `recordStep_mapState_eq` (a renamed configuration from its fields) belongs in
   `StateRenaming`. `recordStep_sweepPost_eq` and `recordStep_seekPost_eq` belong in
   `Contract/Catalog`. `recordStep_fieldOffset_congr` belongs in `Catalog`. All are low
   priority.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 30 | Screen v3 script | SHA-256 `f4feac91…d878f181`, the same in all three worktrees and in the main repository | out/37 |
| 31 | Before | the worker's `screen-before.txt` is byte-equal to the issued base `mig12-fill-cfgrecord-cont1-screen-base.txt`: 870 / 435 / 131,544 | out/25-screen-compare.txt |
| 32 | After (mine; once, `nice -n 10`, under `locks/screen.lock`, 613 s) | `879 declarations; 440 pairs; 133,503 chars`. **Byte-equal to the worker's `screen-after.txt`** | out/25-screen-head.txt, .status |
| 33 | New pairs (`pairdiff.py`, against the issued base) | 6 new, 1 gone, all in-file: <br>• `contract_clauses` ↔ `_range` 84% / 69%; <br>• `probe_run` → `runFrom_one` 77%; <br>• `map_snapshot` → `scan_preserves` 59%; <br>• `read_prefix` → `copyback_run` 54%; <br>• `state_run` → `scan_preserves` 50%; <br>• gone: `position_run` → `copyback_run` 57%. <br>They are line for line REPORT's five items (it counts the 84/69 pair once). The shared texts are the reader's `segment_iff`/`headBox_iff` extraction and the contract-read preamble. **None ≥ 90%** (N1) | out/25-screen-compare.txt |
| 34 | Cross-file pairs, high pairs | none with `CfgRecord` on exactly one side. The only `CfgRecord` pairs ≥ 90% are the pre-existing `Turing.{k#1`/`#2` (100%, at the base too). `CfgRecord` pairs 23 → 28 | same |
| 35 | Lint, `TuringMachine/Build` | `0 FAIL, 30 WARN over 38 files` at the patched base and at the head. Only `CfgRecord`'s size WARN and INFO lines change (5310 → 5712; 98 → 109 private) | out/26 |
| 36 | Widths and whitespace | added lines ≤ 98 characters. Lines over 100: 110 → 95, none new. No trailing whitespace or tab; double blank lines unchanged (12); `git diff --check` clean | out/27 |
| 37 | Docstrings and sketches | all 11 new privates have a docstring. Every new or changed proof over 20 lines has a literal "Proof sketch", except `recordStep_fieldOffset_congr` (F4). 35 added docstring lines: no campaign label, path or date; "public" ×3 and "R1" ×1 (F4) | out/28 |

## (f) Environment (addendum v2.4, Part 1) and the sweep

| Item | Recorded | Evidence |
|---|---|---|
| Preflight (17:49:09Z) | `nproc` 4. cgroup v1 with `memory.limit_in_bytes` 9,223,372,036,854,771,712 (no limit), so the headroom is `MemAvailable` 15,998,596 kB = **15.26 GiB ≥ 4** (v2.4's no-limit rule). For reference, v1 in use = 729,440,256 − 572,010,496 + 15,466,496 = 172,896,256 B. Disk on ext4 `/`: **26,915,348,480 B = 25.07 GiB ≥ 12**; re-check after the toolchain 23,942,975,488 B = 22.30 GiB ≥ 8. The arithmetic checks. **PASS.** Unusual but harmless: `df` reports 270.6 GB blocks but only 14.6 GB used + 26.9 GB available, so the space is capped below the device size; the preflight labels v1's limit as "memory.max" | `evidence/logs/preflight.log` |
| Toolchain | Lean 4.25.0 started normally; no shim, none shipped | REPORT |
| Roots | **61, identical to my extraction** from the 280-module order list at the patched base | out/29 |
| Cache | the narrowed fetch: `Attempting to download 1026 file(s)` → 1026, `Decompressing 1026 file(s)`, `Completed successfully!`, no failure, no retry. Downloaded = unpacked, so the cache store held **no archive beforehand** (v2.5's concern does not arise). The cache executable's 20 Lake jobs are the expected self-build | `cache-get.log` |
| Packages | the clone lines match `lake-manifest.json`: 11 PASS (URL and revision), the 4 doc packages absent (v2.4's "present" reading). REPORT asserts the later checks; there is no verification log (F5.6) | out/30 |
| Bans | no `lake build`; no unfiltered `cache get` (1,026 of ~7,500 files) | logs |
| Bootstrap | the addendum's item-5 split: <br>• the 28 upstream modules, then the owned file (17:55–18:00Z, all exit 0): 12 sorry warnings in 5 modules, the base set's; <br>• the remaining 251 (19:37–20:06Z, before the final sweep, as item 5 allows): 71 in 16; one retry of `Build/RecordTable` after a missing-olean error (F5.9) | out/31 |
| Final sweep (20:07:55–20:37:57Z, after the last commit at 19:51:03Z) | **280/280 in the order list's exact order, all exit 0, 0 errors.** 83 sorry warnings in 21 modules, **name for name the base set**: the only difference is the base file's `[private]` label on `exists_canonGrammarStage`. `CfgRecord` (`CHECK 158/280`) has no diagnostic. All 557 diagnostics outside `CfgRecord` are identical to the bootstrap's (file, line, column, kind, text). Within the 52-module closure: 32 sorry warnings in 5 modules, the base's | out/31, out/36 |

## (g) Landability

- **The owned file is unchanged from the base to the tip** (blob `08fb047f` at the base, at
  `0416ffea` and at the tip; no commit touches it). The six patches apply at `144201de` and
  give `5b1feb62` (out/08).
- **Upstream:** 28 modules, the same set at the head and at the tip. From the base to the tip
  only `Simulation` changed (#132), and `oleans-lsk2` carries the tip's version. The tip
  elaboration is clean (row 13).
- **Replay closure:** `CfgRecord`'s downstream closure is **52 modules** (itself plus 51), the
  same at the base and at the tip; it equals the brief's count (out/35-down-cfgrecord-tip.txt).
  - **The import is what forces the replay.** The private changes cannot reach downstream
    statements. But round 1's import (`Build.Contract`) puts the contract facade into every
    one of the 52 modules' environments.
- **Merged-tree replay** (no snapshot of the tip's tree is recorded):
  - `oleans-lsk2` is `0416ffea`'s tree. Since then the facade, `InputDevice` (#146),
    `SeamLayout` (#145) and `ZoneRebalance` (#148) changed.
  - The downstream closure of those four and `CfgRecord` is **57 modules**: the 52 plus
    `InputDevice`, `SeamLayout`, `ZoneRebalance`, `UniversalK` and `SelfUniversal`
    (`out/35-merged-replay.txt`, in topological order).
  - Expected at the tip: 0 failures; `CfgRecord` 0 warnings; 32 sorry warnings in 5 modules
    within the 52 and 37 in 7 within the 57 (static count; `InputDevice` and `SeamLayout` are
    now proved) (out/36).
- **Overlap with the open PRs** (each closure from its own head's imports, out/35):

  | PR | Changes | Its closure | Shared with this landing's 52 |
  |---|---|---|---|
  | #147 (`28150fc1`) | `UniversalK`, facade | `UniversalK`, `SelfUniversal`, facade | **the facade only** (the standing facade-only rule: no re-replay). `UniversalK`/`SelfUniversal` are in the 57 only through the merges since `lsk2` |
  | #149 (`097f3e04`) | `Deterministic`, `Finite` (37 added lines, no attribute) | 324 modules, everything downstream of `Deterministic` | **all 52**: both files are upstream of `CfgRecord`. Whichever lands second must replay the overlap against the other's merged tree (D1) |

  No other landing touches `Build/CfgRecord`. The two PRs' merge-base with the tip is the tip.

## (h) Recommendation and landing

**Not yet clear to merge**: the landing PR has not been opened, replayed or gated. It becomes
clear once that PR's replay passes, the gate (the swap gate: freeze, replay, fidelity) is
recorded, and the PR's base is the campaign branch.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`, not stacked.

**Commits.** Cherry-pick the whole series, in order, from `refs/review/mig12-cont1`
(prerequisite `96d60278`). The first two are round 1's commits under new hashes; nothing has
merged them. Alternatively, `git am -3` of `patches/0001`–`0006`:
1. `5d02122a07cc88fc7d14a143345eddfdac5a9f6a`: the import;
2. `e1ff1a57d6f4a719d6ad6eefd100c48571fbcd31`: phase 1;
3. `4a756f0bb17f3556b6209c203219ca66d3182311`: phase 2, first part;
4. `8f90ee273bba0972de44b536d100f9fc483ac166`: phase 2 finished, phase 3;
5. `90410caa3f13b8ed05644bb74df8af92153c8a4a`: phase 4;
6. `8b0b0bf4b7e97b4dbb611d91b67fe2b2b248dc34`: line wraps.

The series touches only the owned file. The commit subjects carry campaign labels ("MIG-12",
"phase 2"), as earlier landings' subjects do. Their authorship is mixed (D5).

**Maintainer edits** (one commit in the same PR; public-facing text: no campaign labels, paths
or dates; widths ≤ 100):
1. **Module status** (head lines 28–31), replacing the paragraph:

   > **Status.** Everything here is proved: the pure decoding facts and all three record rows.
   > The rows compose the framed catalog and counter rows through their contracts
   > (`Turing.Contract.segment` and each row's field equations) inside one phase host, and
   > join the phases by `Turing.Segment.trans`. No public result or private helper in this
   > module is admitted.

2. **F3, `exists_recordStepTM`:**
   - at 4681–4682, "now has a `RecordRun` ending at" → "now has a head-bounded segment
     (`Turing.Segment`) ending at";
   - at 4700, "`RecordRun` composes the full cuts and radii" → "`Turing.Segment.trans`
     composes the full cuts and radii".
3. **F3, `exists_recordEqTM`:**
   - at 4937–4938, "run `compareTM` framed (`compareTM_run_ofCfg`)" → "run `compareTM` framed
     (`Turing.compareTM_contract`, whose time is exact)";
   - at 4946, "`recordRun_trans` only concatenates" → "`Turing.Segment.trans` only
     concatenates".
4. **F3, `Cfg.inWindow_init`** (5706): "**Proof sketch.** Unfold `Turing.Cfg.init`." →
   "**Proof sketch.** Read the fields of `Turing.Cfg.init` (`Turing.Cfg.init_workTapePos`,
   `Turing.Cfg.init_workTapes`): every head is at `0` and every cell is blank."
5. **Optional, F2 (D2):** the `recordStep_cell_write` re-proof of `probes/cell-write-fix.diff`
   (+3 lines). Tested in a copy: it elaborates with no output, and S2 is then clean.
6. **Optional, F4:**
   - `recordStep_restrict`: "Reconstruct the selected digit bank through the public R1
     reconstruction lemma." → "Reconstruct the selected digit bank from the
     embed-and-update equation (`recordStep_embed_update`)."
   - "Read the public scan contract" → "Read the scan row's contract";
     "Read the public clear contract" → "Read the clear row's contract".
   - `recordStep_fieldOffset_congr`: insert a literal "**Proof sketch.** Induct on the first
     list; each step is `fieldOffset_cons_succ` with the heads' equal lengths." in place of "no
     retrace of the layout sum".

After the edits:
- re-elaborate the module (expect no output);
- re-run the seal (S1, and S2 if item 5 is taken; `scripts/mkseal2.py`);
- re-lint;
- re-screen. The edits are docstring-only, plus item 5's proof, so expect the same pair set or
  note the difference.

**Replay order** (the worktree needs the `.lake/packages` link):
- **If #149 has not landed:** the 57-module merged-tree replay (`out/35-merged-replay.txt`)
  into a copy of `oleans-lsk2`, with `CfgRecord` pinned at the landed blob. A snapshot of the
  tip's tree, if the maintainer has one by then, needs only the 52.
- **If #149 lands first:** the 52 (plus whatever changed since that snapshot) into #149's
  merged-tree snapshot, since `CfgRecord` must be re-elaborated against the new
  `Deterministic` and `Finite`.
- #147 meets this landing only at the facade, so the order is free.

**Review table for the PR body:**
- integrity: 46/46 sums; bundle on the base; 6 commits; series = bundle = file; round 1's
  patch-ids;
- freeze: 21/21 public statements and docstrings byte-identical; 11 privates added; imports
  unchanged;
- elaboration at the base and at the tip: no output;
- axioms: the standard three, no `sorryAx`, no external private;
- seal S1: 53 definitions, 73 controls; S2: `recordStep_cell_write` only (or clean with item 5);
- probe: 227/227, standalone at the base and at the tip, and in-module;
- screen: 870 → 879 declarations, 435 → 440 pairs, 6 new in-file < 90%, 0 cross-file;
- lint: 0 FAIL;
- sweep: 280/280, 83 = the base set.

## Decisions for the user

- **D1, the landing order against #149.**
  - (a) Land MIG-12 first (recommended if #149's replay has not started). #149's 324-module
    replay then covers `CfgRecord`'s 52 at no extra cost.
  - (b) Land #149 first. This landing then replays its 52 into #149's merged snapshot.
- **D2, F2.**
  - (a) Include the tested 3-line `recordStep_cell_write` re-proof in the landing PR
    (recommended). The landing gate covers it, and rule 10 then holds under simp erasure too.
  - (b) Land as delivered and put the site on the deferred list. It is pre-existing and outside
    the binding ledger.
- **D3, F3: the frozen-docstring rewordings.**
  - (a) The three M2 mentions the brief authorized, plus the two new ones (`compareTM_run_ofCfg`,
    `Cfg.inWindow_init`'s sketch) (recommended).
  - (b) The three only.
- **D4, F1: the size estimate.**
  - (a) Close MIG-12 at its correctness and fidelity targets, and record in design §16 that its
    −1.6k to −2.1k estimate was not met (+410 lines from the base).
  - (b) Schedule a compression item later, which would carry `Segment`s end to end through the
    phase lemmas (`Segment.mono` with `record_headBox_mono`) and drop the scalar envelope
    conversions. Size alone is not a driver, so (a) is the default.
- **D5, commit authorship.** Commits 3–4 carry the user's own address as "Fill Agent"; 5–6
  carry "Claude". Keep them as delivered (workflow §4 preserves the agent's authorship), or
  re-author at cherry-pick.
- **D6, promotion** (the maintainer's window): the contract segment reader first, then
  `MultiTapeTM.runFrom_one` (three copies in the tree).
