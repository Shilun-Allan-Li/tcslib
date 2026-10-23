# MIG-12 continuation 1 — CfgRecord onto the contract layer: fill report

**STATUS: COMPLETE.** Phase 1 landed via the two prescribed patches; phase 2 replaced every
`_run_ofCfg` destructuring by a contract read (the one authorized `counterLoopTM_run_escape`
call retained); phase 3's three rows compose the migrated phase lemmas with their statements
frozen; phase 4 took the ledger's explicit sites from 73 to 0 and certified every
per-definition definitional-site count at 0 by a clean elaboration with all 20 sealable
ledger definitions `local irreducible` at once. The owned file checks with 0 errors and
0 warnings. The file is admission-free; the delivery contains no `sorry`, no `admit`, no
new axiom.

## The brief's checklist

- [x] The preflight's numbers (addendum v2.4, Part 1) — **Preflight** below.
- [x] The base hash, the ancestor check, and the two patches applied (the head file's
      blob) — **Repository, base, patches**.
- [x] What was done: the phase lemmas re-proved, the ledger rows re-pointed, the rows
      re-composed; what remains (nothing) — **Phase 2/3**, **Phase 4**, **the 173 ledger
      rows**.
- [x] The counter-loop exception: `recordStep_save_run`'s one direct use, unchanged in
      route — **Phase 2/3**.
- [x] The seal comparison's per-definition counts and the explicit-site count, before and
      after — **Phase 4** (every after-count 0; explicit 73 → 0).
- [x] The freeze log (21 publics unchanged), the line count before and after — **The owned
      file** (5,310 → 5,712).
- [x] Rule 10 and 11 greps of the diff; the probe re-run; the axiom walks of the three
      rows — **Rule 10 and 11 greps**, **Final sweep, probe, axioms**.
- [x] Duplication: both v3 screens, every new pair justified, the removed pairs —
      **Duplication**.
- [x] The final sweep tail; the axiom prints; the lint line; the checkpoint zips written —
      **Final sweep, probe, axioms**, **The owned file** (lint), **Checkpoints**.

## Preflight (addendum v2.4, Part 1)

- Host: 4 CPUs (`nproc`); cgroup v1 with `memory.limit_in_bytes = 9223372036854771712`
  ("max", no cgroup limit), so the headroom is `MemAvailable` = 15,998,596 kB ≈ 15.26 GiB
  ≥ 4 GiB — PASS. (For reference, v1 in-use = `usage − total_cache + total_shmem` =
  729,440,256 − 572,010,496 + 15,466,496 = 172,896,256 B ≈ 0.16 GiB.)
- Disk (ext4, `/`): 26,915,348,480 B ≈ 25.07 GiB available at the initial preflight
  ≥ 12 GiB — PASS. Re-check after the toolchain, before the cache: 23,942,975,488 B ≈
  22.29 GiB ≥ 8 GiB — PASS.
- No memory-backed filesystem used for the clone, `.lake`, oleans or TMPDIR.
- `/usr/bin/time -v` is not installed on this host; module checks log start/end times
  (the addendum asks for maximum memory "where available").
- Raw numbers: `evidence/logs/preflight.log`.

## Repository, base, patches

- Brief SHA-256 `0ee25ec575151a13c35b198f3c032b17c9ccef533067a8a6649f591f01a92bc5`;
  addendum v2.4 SHA-256 `42555a4f691b378cd3d8ca0fd584717852c333be97aeaf1b6f7cb40b01c5f1d0`;
  the repository copy of the brief matches the attachment byte for byte after replacing
  `@ANCESTOR@` with the base hash.
- Clone: `https://github.com/Shilun-Allan-Li/tcslib`, branch `complexity/arora-barak-ch3-4`
  (observed at `ca7d1feda54f1f5508a1a7c3564ed06235671a15`);
  `git merge-base --is-ancestor 96d60278… HEAD` PASSED.
- Branch `fill/mig12-cfgrecord-cont1` created at exactly
  `96d60278e4fde29b986ec1d0e59cd07f768fe28a` (verified by `git rev-parse HEAD`).
- The two prescribed patches applied with `git am`;
  `git rev-parse HEAD:TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean` =
  `1c9d198f7f1a1ed2c4bdd6ec0a98c1d9a2c88b6c` — the verified first-round head file. `git am`
  of these two patches is the only history operation used; no rebase, merge or cherry-pick.
- Commits on `fill/mig12-cfgrecord-cont1` (bundle prerequisite = the base only):
  1. `5d02122a` / `e1ff1a57` — the two prescribed first-round patches (phase 1).
  2. `4a756f0b`, `8f90ee27` — phase 2/3: every row read through its contract; the three
     rows re-composed.
  3. `90410caa` — phase 4: seal self-check clean; the ledger's `unfold` site re-pointed;
     warnings pruned.
  4. `8b0b0bf4` — the eight over-long proof lines introduced by the swap wrapped.

## Environment

- Lean 4.25.0 (pinned; `lean --version` prints 4.25.0, commit `cdd38ac5…`). **The toolchain
  started normally; Part 2's shim condition did not occur and the shim was neither compiled
  nor used.**
- Narrowed cache: 61 Mathlib roots from the order list
  (`evidence/logs/mathlib-roots.txt`), `TAR_OPTIONS=--no-same-owner lake exe cache get …`:
  1,026/1,026 files downloaded and decompressed, no failed download, no retry
  (`evidence/logs/cache-get.log`). `find .lake/packages -name '*.olean' -size 0` is empty.
  Every present package's origin URL and HEAD equal `lake-manifest.json`'s. Probe importing
  the first root passed through `scripts/lean_check_tree.sh` (exit 0).
- **No `lake build` was run.** All checks go through `scripts/lean_check_tree.sh`, one Lean
  process at a time.
- Bootstrap (addendum Part 1 item 5, recorded): first the 28 order-list modules upstream of
  the owned file, in order, then the owned file — all exit 0 (`evidence/logs/bootstrap.log`).
  The remaining 251 order-list modules were then built, in order, before the final sweep
  (`evidence/logs/bootstrap-remaining.log`, 251/251 exit 0). That build restarted once at
  module 130 (`Build/RecordTable`): the check script prunes a stale olean of an edited
  source, so the owned module was rebuilt from its final text (0 errors, 0 warnings,
  `evidence/logs/check-groupJ.log`) and the build resumed; no module failed.

## Phase 2/3 — the row reads and the three rows

Phase lemmas re-proved over the row contracts (each read through `Contract.segment` via
`segment_iff`/`headBox_iff` plus the row's field equations; the host's verdicts excluded by
stage indices via the retained `record_tag_ne` / `recordStep_tagged_segment`):
- `recordStep_state_run`, `recordStep_scan_preserves` (scanTM_contract);
- `recordStep_clear_snapshot` (clearTM_contract; consumers `recordStep_halt_run`,
  `recordStep_empty_run`, `recordStep_reject_run`, `recordStep_copyback_run` unchanged on
  top of it);
- `recordStep_map_snapshot` (scanTM_contract at scanMap);
- `recordStep_read_prefix` (skipTM_contract, copyTM_contract),
  `recordStep_read_fields` (skipTM_contract, skipBackTM_contract);
- `recordStep_tape_run` (scanTM_contract twice), `recordStep_copyback_run`
  (copyTM_contract), `recordStep_write_back` (skipBackTM_contract);
- `recordStep_apply_run` (scanTM_contract, skipTM_contract);
- inside `exists_recordEqTM`: skipTM_contract, skipBackTM_contract, and
  **compareTM_contract** (exact time `2·compareStop+2`; the old existential bound recovered
  by `compareStop_le`);
- inside `exists_recordTestTM`: scanTM_contract (fold), skipTM_contract,
  skipBackTM_contract.

The three public rows `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM`
re-compose these phase lemmas; their statements (and all 21 frozen publics) are
byte-identical to the patched base (freeze log below).

**Counter-loop exception:** `recordStep_save_run` keeps its single direct
`counterLoopTM_run_escape` call, unchanged in route (MIG-15 owns its contract form).

New private declarations (kit additions, each with a docstring; 11 in all):
- `recordStep_contract_clauses` — reads a one-exit row contract as run equation,
  first-exit cut and per-tape envelope (from `Contract.segment` via `segment_iff` and
  `headBox_iff`; no retrace).
- `recordStep_contract_clauses_range` — the same for verdict-range exits (scan, compare).
- `recordStep_sweepPost_eq`, `recordStep_seekPost_eq` — the sweep/seek endpoints as the
  record literals the proofs match on, assembled from their published field equations.
- `recordStep_mapState_eq`, `recordStep_mapState_mk`, `recordStep_mapState_snapshot` —
  field-by-field renaming equalities through `Cfg.mapState_*`, replacing every explicit
  `Cfg.mapState` simp site and converting snapshot renamings at the segment joints.
- `recordStep_runFrom_one`, `recordStep_orbit_one_step` — one unit-length round is one
  machine step, by the published `runFrom`/orbit equations.
- `recordStep_embed_update` — the one-step embed-and-update record equality behind
  `recordStep_restrict`, through `embedEmitCfg_eq` and the `Cfg.liftSymbols_*` equations.
- `recordStep_fieldOffset_congr` — the `j`-th field offset reads only the lengths of the
  first `j` fields (from `fieldOffset_zero`/`fieldOffset_cons_succ`); replaces the ledger's
  `unfold fieldOffset` row in `exists_recordEqTM` and the local length-equality induction
  in `exists_recordStepTM`.

## Phase 4 — the unfolding sites

**Explicit sites: 73 → 0.** On the patched base the scan finds 73 explicit sites of ledger
definitions: 70 tactic-bracket-list entries plus 3 `unfold` targets (two
`FinTM.bufferTape`, one `fieldOffset`). On the delivered file the same scan finds **0**
bracket-list entries and **0** `unfold`/`delta` targets. (The surviving mentions of ledger
names are statement spellings inside `show … from <published lemma>` ascriptions — the
goal restated with the name, closed by the published lemma, no reduction of the
definition; the all-sealed run below certifies this, since every such `rfl`/`from` closes
with the definition irreducible.)

**Definitional sites: every per-definition count 0.** The seal self-check puts
`attribute [local irreducible]` on all 20 sealable ledger definitions at once in a scratch
copy of the module and elaborates it. The final copy elaborates with **zero errors**
(`evidence/logs/seal-all7.log`, on the delivered text; also `seal-all6.log` one wrap
earlier). A clean all-sealed run bounds every per-definition count by 0:

| Definition | Base count (brief) | After |
|---|---:|---:|
| `Cfg.mapState` | 27 | 0 |
| `Cfg.liftSymbols` | 20 | 0 |
| `MultiTapeTM.runFrom` | 15 | 0 |
| `embedEmitCfg` | 12 | 0 |
| `fieldOffset` | 7 | 0 |
| `Action.apply` | 6 | 0 |
| `roundOrbit` | 3 | 0 |
| `FinTM.bufferTape`, `Cfg.inputSymbol`, `incFixed`, `scanKeep`, `scanFold`, `counterWord`, `Cfg.init` | 1 each | 0 each |
| the remaining sealable ledger definitions | 0 | 0 |

Fix-round error ladder of the all-sealed probe: 77 → 44 → 14 → 5 → 1 → 0. The last
survivor (a `decide`-instance mismatch at the `round` cell-word endpoint in
`exists_recordStepTM`'s host) was removed by generalizing the field-word equation over the
configuration (`cellWord`) and instantiating it at `a.apply c`, so no default-simp pass
runs over an `Action.apply` application there.

(`counterLoopOrbit` is a reducible abbreviation and cannot be made irreducible; its ledger
rows were re-pointed to the published `roundOrbit` equations via `show`-ascribed rewrites,
and the sealed `roundOrbit` certifies them.)

**The per-row disposition of all 173 ledger rows is the table at the end of this report.**

## The owned file

- `evidence/logs/check-groupJ.log`: the delivered module elaborates with **0 errors and
  0 warnings** (the patched base also had 0 warnings), no `sorry`.
- Line count: base (after the patches) 5,310 → delivered **5,712** (+402). The design
  estimated −1.6k…−2.1k; the actual delta is **positive**, reported as such: the swap
  reads the rows through their contracts without compressing the surrounding scalar
  bookkeeping (the window, offset and digit arithmetic stands as before), and the kit
  gained eleven shared readers/bridges plus their docstrings. The compression the estimate
  anticipated was in the retired `RecordRun` kit (phase 1, already in the patches'
  figures), not in the row reads.
- Declarations: 21 public (frozen) unchanged; privates 98 → 109 (the 11 kit lemmas above;
  none removed, none merged).
- Freeze: `freeze-check` over the 21 frozen publics (docstring + statement, byte compare
  against the patched base) — **FREEZE PASS (21 names, 0 problems)**, re-run on the
  delivered text.
- Lint: `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  → **0 FAIL, 30 WARN over 38 files** (the base line exactly). Long lines: 151, all
  present in the patched base; **no new line over 100 characters** (the eight the swap
  had introduced were wrapped in `8b0b0bf4`).

## Rule 10 and 11 greps of the diff

- Rule 11: `grep` of the swap diff's added lines for the six R3 canonical rows
  (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
  `incrementTM_run_overflow`) — **no hit**. No private of `Build/Catalog` is named
  anywhere in the file (and none is reachable, per the axiom walk below).
- Rule 10: `grep` of the added lines for `unfold`/`delta` — **no hit** (the diff removes
  the base's three ledger-definition unfolds and adds none).

## Final sweep, probe, axioms

- Final sweep (`evidence/logs/final-sweep.log`): every module of the 280-module order
  list, in order, through `scripts/lean_check_tree.sh` — **280/280 exit 0, 0 errors**;
  the owned module contributes **no diagnostic line** (0 errors, 0 warnings). The
  non-sorry warnings in the log belong to untouched modules and are the base's own.
- Sorry set vs the base inventory (83 warnings in 21 modules): **exactly the base's** —
  83 `declaration uses 'sorry'` warnings in the same 21 modules, per-module counts equal
  (`evidence/logs/sorries-compare.log`); none in the owned file.
- Import probe (`MIG12ImportProbe`, 227 names) re-run on the final import context:
  **exit 0, 0 errors** (`evidence/logs/import-probe.log`).
- Axiom prints for the 21 publics and the 11 new privates (`evidence/logs/axioms.log`):
  **all 32 within `[propext, Classical.choice, Quot.sound]`** (several need fewer; ten
  need none).
- Axiom walk of the three rows and the 11 kit lemmas (`evidence/logs/axioms.log`, the
  `WALK` lines): the terms of the owned module's own declarations are walked, imported
  constants treated as boundaries — **no root references any other module's private
  declaration**. In particular the two privates of `Build/Embed` that
  `exists_recordStepTM` reached at the base through the legacy definitional reading of
  `embedEmitCfg` (`embedSlot`, `embedActionCore.match_3`) are **gone**: the re-pointing
  through `embedEmitCfg_eq` removed both. (Rule 11's second half is confirmed the same
  way: no private of `Build/Catalog` is referenced from any root.)

## Duplication (v3 screens, binding)

Both screens ran one at a time under `nice -n 10` over the brief's 12-file population.
- **Before** (patched, pre-phase-2 tree): 870 declarations, 435 pairs, 131,544 reproduced
  characters — **equal to the supplied base log** (`evidence/logs/screen-before.txt`).
- **After** (delivered tree): 879 declarations, 440 pairs, 133,503 reproduced characters
  (`evidence/logs/screen-after.txt`).
- **New pairs** (all with the owned file on both sides, all below the 90% copy bar, none
  factored):
  1. `recordStep_contract_clauses` ↔ `recordStep_contract_clauses_range` (84%/69%) — the
     two exit-shape readers (singleton exit vs verdict-range exit); they share the
     `segment_iff`/`headBox_iff` clause extraction and differ in the cut-witness shape;
     kept separate because the exit-set types differ.
  2. `recordStep_probe_run` → `recordStep_runFrom_one` (77%; 73/95 characters) — the
     shared published-API idiom (`runFrom_succ_eq_step'` + `runFrom_zero`); the probe
     needs the `t = 1` instance, which the `t = 0` kit reader does not provide, and it
     already calls `recordStep_runFrom_one` at its two one-step sites.
  3. `recordStep_map_snapshot` → `recordStep_scan_preserves` (59%) — both read
     `scanTM_contract` through `recordStep_contract_clauses_range` with the same
     stage-index exclusion preamble; the postconditions differ (map vs preserve).
  4. `recordStep_read_prefix` → `recordStep_copyback_run` (54%) — both read the copy/skip
     rows through `recordStep_contract_clauses`; the shared text is the contract-read
     preamble.
  5. `recordStep_state_run` → `recordStep_scan_preserves` (50%) — both `scanTM_contract`
     reads; shared preamble, at the bar's edge.
- **Removed pair**: `recordStep_position_run` → `recordStep_copyback_run` (the swap
  rewrote `recordStep_position_run`'s read).

## Checkpoints and escalations

- Checkpoint zips written: `fill-mig12-cfgrecord-cont1-cp1.zip` (after phase 2's row
  reads), `fill-mig12-cfgrecord-cont1-cp2.zip` (after phase 4's seal convergence), and
  the final `fill-mig12-cfgrecord-cont1.zip`.
- **No escalations**: no ground rule blocked an item; every ledger row was re-pointed
  through published lemmas (one via the new in-file kit lemma
  `recordStep_fieldOffset_congr`, itself assembled from published lemmas).

## The 173 ledger rows

| Base line | Declaration | Definition | Kind | Disposition |
|---:|---|---|---|---|
| 407 | `recordRun_zero` | `MultiTapeTM.runFrom` | implicit | declaration retired by the phase-1 patches (`RecordRun` and its kit removed) |
| 441 | `record_tag_ne` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 444 | `record_tag_ne` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 465 | `recordRun_tagged` | `Cfg.mapState` | implicit | declaration retired by the phase-1 patches (`RecordRun` and its kit removed) |
| 529 | `recordStep_digits_succ` | `counterWord` | implicit | definitional reliance removed (certified by the all-sealed run, `counterWord` irreducible); the surrounding proof reads counterWord_succ, counterWord_zero (round 3) |
| 541 | `recordStep_digits_succ` | `decFixed` | explicit | explicit site removed; the proof reads decFixed_nil/_true_cons/_false_cons (#118) |
| 545 | `recordStep_digits_succ` | `decFixed` | explicit | explicit site removed; the proof reads decFixed_nil/_true_cons/_false_cons (#118) |
| 547 | `recordStep_digits_succ` | `incFixed` | implicit | definitional reliance removed (certified by the all-sealed run, `incFixed` irreducible); the surrounding proof reads incFixed_nil/_false_cons/_true_cons (MIG-12 API) |
| 550 | `recordStep_digits_succ` | `decFixed` | explicit | explicit site removed; the proof reads decFixed_nil/_true_cons/_false_cons (#118) |
| 552 | `recordStep_digits_succ` | `decFixed` | explicit | explicit site removed; the proof reads decFixed_nil/_true_cons/_false_cons (#118) |
| 554 | `recordStep_digits_succ` | `incFixed` | explicit | explicit site removed; the proof reads incFixed_nil/_false_cons/_true_cons (MIG-12 API) |
| 589 | `recordStep_window` | `Action.apply` | implicit | definitional reliance removed (certified by the all-sealed run, `Action.apply` irreducible); the surrounding proof reads Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 591 | `recordStep_window` | `Action.apply` | implicit | definitional reliance removed (certified by the all-sealed run, `Action.apply` irreducible); the surrounding proof reads Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 598 | `recordStep_window` | `Action.apply` | explicit | explicit site removed; the proof reads Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 618 | `recordStep_restrict` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 618 | `recordStep_restrict` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 619 | `recordStep_restrict` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 619 | `recordStep_restrict` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 625 | `recordStep_restrict` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 632 | `recordStep_restrict` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 637 | `recordStep_restrict` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 638 | `recordStep_restrict` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 639 | `recordStep_restrict` | `Cfg.liftSymbols` | explicit | explicit site removed; the proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 639 | `recordStep_restrict` | `embedEmitCfg` | explicit | explicit site removed; the proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 666 | `recordStep_native_frame` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 717 | `recordStep_read_run` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 743 | `recordStep_save_orbit` | `roundOrbit` | implicit | definitional reliance removed (certified by the all-sealed run, `roundOrbit` irreducible); the surrounding proof reads roundOrbit_zero/_succ |
| 747 | `recordStep_save_orbit` | `counterLoopOrbit` | explicit | explicit site removed; the proof reads roundOrbit_zero/_succ, through the abbreviation (exact / simp only; N3) |
| 747 | `recordStep_save_orbit` | `roundOrbit` | explicit | explicit site removed; the proof reads roundOrbit_zero/_succ |
| 748 | `recordStep_save_orbit` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 748 | `recordStep_save_orbit` | `roundOrbit` | implicit | definitional reliance removed (certified by the all-sealed run, `roundOrbit` irreducible); the surrounding proof reads roundOrbit_zero/_succ |
| 760 | `recordStep_save_orbit` | `counterLoopOrbit` | explicit | explicit site removed; the proof reads roundOrbit_zero/_succ, through the abbreviation (exact / simp only; N3) |
| 760 | `recordStep_save_orbit` | `roundOrbit` | explicit | explicit site removed; the proof reads roundOrbit_zero/_succ |
| 761 | `recordStep_save_orbit` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 761 | `recordStep_save_orbit` | `roundOrbit` | implicit | definitional reliance removed (certified by the all-sealed run, `roundOrbit` irreducible); the surrounding proof reads roundOrbit_zero/_succ |
| 766 | `recordStep_save_orbit` | `Cfg.inputSymbol` | explicit | explicit site removed; the proof reads Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 776 | `recordStep_input_blank` | `Cfg.inputSymbol` | explicit | explicit site removed; the proof reads Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 778 | `recordStep_input_blank` | `Cfg.inputSymbol` | explicit | explicit site removed; the proof reads Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 821 | `recordStep_probe_run` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 827 | `recordStep_probe_run` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 831 | `recordStep_probe_run` | `moveInputPos` | explicit | explicit site removed; the proof reads moveInputPos_zero/_leftBoundary/_rightBoundary/_neg_of_ne_left/_pos_of_ne_right |
| 839 | `recordStep_probe_run` | `moveInputPos` | explicit | explicit site removed; the proof reads moveInputPos_zero/_leftBoundary/_rightBoundary/_neg_of_ne_left/_pos_of_ne_right |
| 853 | `recordStep_probe_run` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 1189 | `recordStep_cell_shift` | `scanFold` | implicit | definitional reliance removed (certified by the all-sealed run, `scanFold` irreducible); the surrounding proof reads scanResult_keep_keep (round 3) |
| 1189 | `recordStep_cell_shift` | `scanKeep` | implicit | definitional reliance removed (certified by the all-sealed run, `scanKeep` irreducible); the surrounding proof reads scanResult_keep_keep (round 3) |
| 1258 | `recordStep_tape_word` | `Action.apply` | implicit | definitional reliance removed (certified by the all-sealed run, `Action.apply` irreducible); the surrounding proof reads Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 1520 | `recordStep_state_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1522 | `recordStep_state_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1524 | `recordStep_state_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1579 | `recordStep_phase_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1671 | `recordStep_read_prefix` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 1676 | `recordStep_read_prefix` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 1682 | `recordStep_read_prefix` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 1731 | `recordStep_read_prefix` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1782 | `recordStep_read_prefix` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1803 | `recordStep_read_prefix` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 1835 | `recordStep_read_prefix` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1850 | `recordStep_read_prefix` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1996 | `recordStep_read_fields` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2047 | `recordStep_read_fields` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2094 | `recordStep_read_fields` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2150 | `recordStep_read_fields` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2160 | `recordStep_read_fields` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 2180 | `recordStep_read_fields` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 2211 | `recordStep_read_all` | `fieldOffset` | implicit | definitional reliance removed (certified by the all-sealed run, `fieldOffset` irreducible); the surrounding proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 2253 | `recordStep_clear_snapshot` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2308 | `recordStep_halt_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2335 | `recordStep_halt_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2338 | `recordStep_halt_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2388 | `recordStep_seek_transport` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2392 | `recordStep_seek_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2392 | `recordStep_seek_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2398 | `recordStep_seek_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2409 | `recordStep_seek_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2409 | `recordStep_seek_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2410 | `recordStep_seek_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2410 | `recordStep_seek_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2412 | `recordStep_seek_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2412 | `recordStep_seek_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2414 | `recordStep_seek_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2414 | `recordStep_seek_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2416 | `recordStep_seek_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2416 | `recordStep_seek_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2454 | `recordStep_map_snapshot` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2456 | `recordStep_map_snapshot` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2499 | `recordStep_empty_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2525 | `recordStep_reject_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2601 | `recordStep_save_transport` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2604 | `recordStep_save_transport` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2618 | `recordStep_save_transport` | `Cfg.liftSymbols` | explicit | explicit site removed; the proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2618 | `recordStep_save_transport` | `embedEmitCfg` | explicit | explicit site removed; the proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2620 | `recordStep_save_transport` | `Cfg.liftSymbols` | explicit | explicit site removed; the proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2620 | `recordStep_save_transport` | `embedEmitCfg` | explicit | explicit site removed; the proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2627 | `recordStep_save_transport` | `Cfg.liftSymbols` | explicit | explicit site removed; the proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2630 | `recordStep_save_transport` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2639 | `recordStep_save_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2640 | `recordStep_save_transport` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2641 | `recordStep_save_transport` | `Cfg.liftSymbols` | explicit | explicit site removed; the proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2641 | `recordStep_save_transport` | `embedEmitCfg` | explicit | explicit site removed; the proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2644 | `recordStep_save_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2644 | `recordStep_save_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2658 | `recordStep_save_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2661 | `recordStep_save_transport` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2791 | `recordStep_prepare_native` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2792 | `recordStep_prepare_native` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2860 | `recordStep_seek_read` | `Cfg.inputSymbol` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.inputSymbol` irreducible); the surrounding proof reads Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 2860 | `recordStep_seek_read` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2883 | `recordStep_seek_read` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2954 | `recordStep_arithmetic_transport` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2956 | `recordStep_arithmetic_transport` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2976 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2976 | `recordStep_arithmetic_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2977 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2977 | `recordStep_arithmetic_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2982 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | explicit | explicit site removed; the proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2990 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2993 | `recordStep_arithmetic_transport` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2994 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | explicit | explicit site removed; the proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2994 | `recordStep_arithmetic_transport` | `embedEmitCfg` | explicit | explicit site removed; the proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2997 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2997 | `recordStep_arithmetic_transport` | `embedEmitCfg` | implicit | definitional reliance removed (certified by the all-sealed run, `embedEmitCfg` irreducible); the surrounding proof reads embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 3006 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.liftSymbols` irreducible); the surrounding proof reads Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 3009 | `recordStep_arithmetic_transport` | `MultiTapeTM.runFrom` | implicit | definitional reliance removed (certified by the all-sealed run, `MultiTapeTM.runFrom` irreducible); the surrounding proof reads runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 3087 | `recordStep_restore_digits` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3113 | `recordStep_restore_digits` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3117 | `recordStep_restore_digits` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3157 | `recordStep_restore_native` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3215 | `recordStep_restore_native` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3216 | `recordStep_restore_native` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3221 | `recordStep_restore_native` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3327 | `recordStep_observed_action` | `Cfg.workTapeSymbols` | explicit | explicit site removed; the proof reads Cfg.workTapeSymbols_eq |
| 3335 | `recordStep_observed_action` | `MultiTapeTM.step` | explicit | explicit site removed; the proof reads MultiTapeTM.step_of_some (round 3), step_of_halt |
| 3337 | `recordStep_observed_action` | `MultiTapeTM.outputSymbol` | explicit | explicit site removed; the proof reads MultiTapeTM.outputSymbol_of_some (round 3), outputSymbol_of_halt, step_output |
| 3369 | `recordStep_tape_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3397 | `recordStep_tape_run` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 3459 | `recordStep_tape_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3462 | `recordStep_tape_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3483 | `recordStep_copyback_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3529 | `recordStep_copyback_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3532 | `recordStep_copyback_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3617 | `recordStep_write_back` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3629 | `recordStep_write_back` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3631 | `recordStep_write_back` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 3706 | `recordStep_position_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3744 | `recordStep_position_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3753 | `recordStep_position_run` | `Cfg.mapState` | explicit | explicit site removed; the proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3764 | `recordStep_position_run` | `Action.apply` | implicit | definitional reliance removed (certified by the all-sealed run, `Action.apply` irreducible); the surrounding proof reads Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 3843 | `recordStep_apply_run` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 3915 | `recordStep_apply_run` | `FinTM.bufferTape` | explicit | explicit site removed; the proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 4019 | `recordStep_apply_run` | `Action.apply` | implicit | definitional reliance removed (certified by the all-sealed run, `Action.apply` irreducible); the surrounding proof reads Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 4024 | `recordStep_apply_run` | `fieldOffset` | implicit | definitional reliance removed (certified by the all-sealed run, `fieldOffset` irreducible); the surrounding proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4026 | `recordStep_apply_run` | `fieldOffset` | implicit | definitional reliance removed (certified by the all-sealed run, `fieldOffset` irreducible); the surrounding proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4034 | `recordStep_apply_run` | `fieldOffset` | implicit | definitional reliance removed (certified by the all-sealed run, `fieldOffset` irreducible); the surrounding proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4037 | `recordStep_apply_run` | `fieldOffset` | implicit | definitional reliance removed (certified by the all-sealed run, `fieldOffset` irreducible); the surrounding proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4042 | `recordStep_apply_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4100 | `recordStep_apply_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4101 | `recordStep_apply_run` | `fieldOffset` | implicit | definitional reliance removed (certified by the all-sealed run, `fieldOffset` irreducible); the surrounding proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4120 | `recordStep_apply_run` | `Action.apply` | implicit | definitional reliance removed (certified by the all-sealed run, `Action.apply` irreducible); the surrounding proof reads Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 4154 | `recordStep_apply_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4200 | `recordStep_apply_run` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4220 | `recordStep_apply_run` | `FinTM.bufferTape` | implicit | definitional reliance removed (certified by the all-sealed run, `FinTM.bufferTape` irreducible); the surrounding proof reads FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 4220 | `recordStep_apply_run` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4263 | `recordStep_apply_run` | `fieldsTape` | explicit | explicit site removed; the proof reads fieldsTape_of_nonneg/_of_neg/_nil/_cons_shift/_field/_of_length_le |
| 4264 | `recordStep_apply_run` | `fieldsTape` | explicit | explicit site removed; the proof reads fieldsTape_of_nonneg/_of_neg/_nil/_cons_shift/_field/_of_length_le |
| 4385 | `exists_recordStepTM` | `fieldOffset` | implicit | definitional reliance removed (certified by the all-sealed run, `fieldOffset` irreducible); the surrounding proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4635 | `exists_recordEqTM` | `fieldOffset` | explicit | explicit `unfold` removed; the proof reads the new kit's `recordStep_fieldOffset_congr` (from `fieldOffset_zero`/`fieldOffset_cons_succ`) |
| 4686 | `exists_recordEqTM` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4904 | `exists_recordEqTM` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4920 | `exists_recordEqTM` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 5119 | `exists_recordTestTM` | `Cfg.mapState` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.mapState` irreducible); the surrounding proof reads Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 5265 | `exists_recordTestTM` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 5284 | `exists_recordTestTM` | `fieldOffset` | explicit | explicit site removed; the proof reads fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 5300 | `Cfg.inWindow_init` | `Cfg.init` | implicit | definitional reliance removed (certified by the all-sealed run, `Cfg.init` irreducible); the surrounding proof reads Cfg.init_state/_inputPos/_workTapes/_workTapePos/_output |

173 rows: 76 explicit, 95 definitional, 2 on retired declarations.
