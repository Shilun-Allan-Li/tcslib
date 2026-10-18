# Review — MIG-12, the `CfgRecord` migration (`Build/CfgRecord.lean`), delivery `fill-mig12-cfgrecord.zip`

**Verdict: partial (phase 1 of 4), correct and admission-free. Landable, but I recommend
folding it into the continuation rather than paying a 52-module replay for it alone (decision
D1).** The delivery:
- adds the authorized import (the first commit, alone);
- retires `RecordRun` and its kit onto the contract layer's `Segment`:
  - one private `abbrev RecordSeg`, exactly the brief's `Segment R {some yes, some no}
    (HeadBox (base − r) (base + r))`;
  - two box/radius bridges;
  - a scalar reader `recordSeg_iff`;
  - the renamed tagged helper;
- replaces every `recordRun_zero`/`_trans`/`_mono` use by `Segment.zero`/`.trans`/`.mono`;
- re-points 5 of the 173 ledger rows.

Phases 2–4 are not started: every phase lemma keeps its original row proof, and 168 ledger rows
remain. The net change is +8 lines (the design estimate for the whole migration is −1.6k to
−2.1k).

What passes:
- every integrity, ownership and freeze check. The 21 public docstrings and statements are
  byte-identical, and the 17 changed private statements differ only by `RecordRun` →
  `RecordSeg`;
- the residual diff: no row proof changed beyond the mechanical swap;
- elaboration (0 errors, 0 warnings), and every axiom set within `[propext, Classical.choice,
  Quot.sound]`;
- a file-wide seal of `Segment` and `HeadBox`: the new layer is read only through its API;
- the per-definition seal comparison and the explicit-site count: exactly the 5 rows REPORT
  claims are gone, and there is no new site anywhere;
- the import probe (227/227) and lint;
- the v3 screen: 870 declarations, 437 → 435 pairs, 0 new; mine is byte-equal to the worker's;
- elaboration at the stack top.

Findings:
- **M1 (progress).** Only phase 1. The swap gate's "fidelity" criterion (contracts read through
  their fields, no hand trace, no unfolding) is not yet met: 29 phase lemmas still destructure
  `_run_ofCfg` and 168 unfolding sites remain. REPORT says so, row by row, and gives the
  resource reason (an OOM kill, disconnects).
- **M2 (text).** Two frozen public docstrings still name the retired `RecordRun`/
  `recordRun_trans`, three times:
  - `exists_recordStepTM` (head lines 4317, 4335);
  - `exists_recordEqTM` (4579).

  The brief allows a flagged "Migration appendix (MIG-12)" on the three rows. The worker added
  none, so the stale words need either that appendix or maintainer wording at integration.
- **No escalation** is raised, and none is needed for phase 1.

## Inputs

| Input | Identity |
|---|---|
| Zip | `infra_local/fill-mig12-cfgrecord.zip`, SHA-256 `1a717199…8ae102` (`zip-sha.txt`); 13 entries (`zip-list.txt`) |
| Extraction | `$S/incoming/mig12-cfgrecord/`: every member byte-equal to the zip, no unsafe entry, no symlink, CRC OK (`zip-vs-extracted.txt`) |
| Brief | `infra_local/fill-dispatches/mig12-fill-cfgrecord.md`, `d815282a…b02d247`; the base's (and `wt-hk`'s) `briefs/mig12-fill-cfgrecord.md` with its three `@ANCESTOR@` → base are byte-equal to it (`brief-check.txt`); REPORT quotes the same hash |
| Addendum | v1, `a25474c5…8d2928`, byte-equal to the base's copy (`brief-check.txt`) |
| Base | `94b986d4db7167ab2a8b20d38d4385f11e60be0e` (Lean = `531b98a2`) |
| Inputs at the base | `audits/evidence/mig12-fill/` (probe, inventory, `unfold-sites.tsv`, `frozen-publics.txt`, population, `replay-closure.txt`), `audits/evidence/mig12/DESIGN.md`, `audits/logs/mig12-fill-*` |
| Snapshots | `oleans-lbapi4` (base), `oleans-lx2` (stack top `5333b29bf1032ccf8f754b389db303f641d9c59b`) |
| Review ref and worktrees | `refs/review/mig12-cfgrecord` (from the bundle). Detached worktrees under this folder: `wt-base`, `wt-head`, `wt-tipd` (stack top plus the two patches), each with the `.lake/packages` link |

Paths below are relative to `$S/review/mig12-cfgrecord-fill/`. Lean ran only through
`tools/leanelab.sh`, one elaboration at a time; the screen ran alone under `nice -n 10`; no build
command was run; the shim (`985924ad…4fba7`) was neither compiled nor run. I read the whole diff
before elaborating (1,174 lines; the rest of the file is the base's).

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | `SHA256SUMS` | PASS: 12/12 OK; covers every member except itself | `sha256sums-check.txt` |
| 2 | Bundle | PASS: `verify` okay; sole prerequisite `94b986d4…`; one ref `fill/mig12-cfgrecord` = `41d31d09e4c8ff9fd645bfa338fbc34e2a4b818d` (REPORT's head) | `bundle-verify.txt` |
| 3 | Commits | PASS: two. `61c25b247918bbccdc04e524a75c4836fbe1c4bd` (parent: the base) adds exactly `import TCSlib.Complexity.TuringMachine.Build.Contract`, the brief's prescribed first edit (`commit1.diff`). `41d31d09` (parent: `61c25b24`) is the swap (+197/−190). Each changes only `Build/CfgRecord.lean` | `head-commit.txt` |
| 4 | Patches | PASS: `0001` at the base gives `61c25b24`'s tree `4b4aef1b`; then `0002` gives the head tree `25345578` | `patch-check.txt` |
| 5 | Delivered file | PASS: byte-equal to the head blob `1c9d198f` (SHA-256 `f0a8e71e…3e7aab`) | `file-agreement.txt` |
| 6 | Freeze, publics (`declfreeze.py`) | PASS: 21 → 21, none added or removed, no statement changed. The "UNAUTHORIZED BODY CHANGE" lines are the three rows, whose bodies the brief owns | `declfreeze.txt` |
| 7 | Publics byte for byte | PASS: for all 21 names of `frozen-publics.txt`, docstring plus statement (text before the first `:=`) is byte-identical | `swapstmt.txt` |
| 8 | Private statements | 17 changed; **every one is exactly `RecordRun` → `RecordSeg`**. The statement is taken up to the proof's `:= by`, so `let … :=` inside statements is included (`scripts/swapstmt2.py`). `privstmt.py`'s coarser cut lists 12 of them | `swapstmt2.txt`, `privstmt.txt` |
| 9 | Declarations | 98 → 98 private. Deleted: `RecordRun`, `recordRun_zero`, `recordRun_trans`, `recordRun_mono`, `recordRun_tagged`. Added: `RecordSeg` (abbrev), `record_headBox_iff`, `recordSeg_iff`, `record_headBox_mono`, `recordStep_tagged_segment` (the renamed `recordRun_tagged`). No public added | `declfreeze.txt` |
| 10 | **Retained row proofs untouched** | PASS. After the three mechanical renames (`RecordRun`→`RecordSeg`, `recordRun_trans`→`Segment.trans`, `recordRun_tagged`→`recordStep_tagged_segment`), 38 hunks remain, all of the swap's kinds (list below). No row call, `_run_ofCfg` destructuring, host argument or arithmetic changed | `residual-diff.txt` |
| 11 | Hygiene (198 added lines) | PASS: no `sorry`/`admit`/`axiom`/`unfold`/`delta`/`set_option`/`native_decide`/`open`/`section`/`variable`/attribute | `hygiene.txt` |
| 12 | Rule 11 | PASS: no R3 row anywhere in the head file (0 hits); no `Build/Catalog` private is reached from any of the three rows (row 20) | `hygiene.txt`, `ax-rows.out` |
| 13 | Imports | PASS: exactly the one authorized line | `hygiene.txt` |
| 14 | Widths | PASS: added lines at most 100. The file's over-100 lines fall from 117 (base) to 112; all are pre-existing | `hygiene.txt` |
| 15 | Size | 5,302 → 5,310 lines; 21 public / 98 private (unchanged counts) | `lint-build-head.out` |

**The residual hunks (row 10), by kind:**
- the kit (base 394–470): the abbrev, the bridges, `recordSeg_iff`, the helper's rename and its
  `rw [recordSeg_iff]`;
- `recordRun_zero … h` → `Segment.zero ((record_headBox_iff _ _ _).mpr h)` (6 sites);
- `recordRun_mono h r` and the anonymous-constructor weakenings `⟨h.1, h.2.1, …⟩` →
  `Segment.mono h (fun _ hx => hx) (record_headBox_mono r)` (13 sites, including the `shift`
  helper of `recordStep_apply_run`);
- `(recordSeg_iff …).mp` conversions back to the frozen scalar clauses in the three rows
  (4 sites, plus `rw [hstart, recordSeg_iff]`);
- the re-pointings: `record_tag_ne` (2), `recordStep_tagged_segment`'s endpoint step, and
  `recordStep_phase_run` (1);
- line rewraps.

**Fidelity of the abbreviation.** `recordSeg_iff` proves `RecordSeg … ↔` the old `RecordRun`
body verbatim (run equation, the two-verdict cut, the absolute radius). Every consumer
therefore sees the same predicate as before. It is proved by `simp only [RecordSeg,
segment_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, record_headBox_iff]`, and
`record_headBox_iff` by `headBox_iff`, `Finset.mem_Icc` and `abs_le`.

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 16 | Head against `oleans-lbapi4` | PASS: exit 0, no error, **no warning** (27 s, 2.4 GB peak) | `elab-head-lbapi4.out` |
| 17 | Base baseline | exit 0, no output | `elab-base-lbapi4.out` |
| 18 | Control | a copy with an appended false `rfl` reports its error; the file is really elaborated | `elab-control.out` |
| 19 | Axioms (in-module copy) | PASS: all 21 publics within `[propext, Classical.choice, Quot.sound]` (5 depend on no axiom); the 5 new privates `[propext, Classical.choice, Quot.sound]`; no `sorryAx` in any closure. Equal to the worker's `axioms.log` | `ax-head.out` |
| 20 | External privates, equation lemmas | none reached from the 5 new privates. From the three rows: `exists_recordStepTM` reaches two privates of `Build/Embed` (`embedSlot`, `embedActionCore.match_3`), **identically at the base**. This is the legacy definitional reading of `embedEmitCfg` (the ledger's 17 rows), for phase 4. `exists_recordEqTM`/`exists_recordTestTM`: none | `ax-head.out`, `ax-rows.out`, `ax-rows-base.out` |
| 21 | Import probe (`MIG12ImportProbe.lean.txt` appended to the delivered module) | PASS: 0 errors, 0 warnings, 227/227 outputs | `probes/MIG12Import-head.out` |
| 22 | Worker's sweep | consistent: 279/279 modules exit 0 in the final sweep. The four-error first attempt at `CfgRecord` (rewrite failures at the scalar conversions) is retained in the log, followed by the corrected retry. The base sorry set is 83 entries in 21 modules, none in `CfgRecord`. Not reproducible here (no build) | `evidence/final-sweep.log` |

## (c) Progress

| Phase | State | Notes |
|---|---|---|
| 1: `RecordRun` retired onto `Segment` | **complete** | none remains in code (three docstring mentions, M2). The abbreviation is stated once, as the brief prescribes. Zero/trans/mono are the shared lemmas. The tagged helper is a statement over `Segment`; `recordStep_phase_run` calls `phaseHostTM_run` once per invocation |
| 2: phase lemmas as contract compositions | **not started** | all 29 phase lemmas keep `_run_ofCfg` destructuring and their local arguments; no `Contract.segment`, `inPhase` or `Cfg.bindState` is used |
| 3: the three rows re-composed | mechanical only | they compose `RecordSeg` over the unchanged phase lemmas and convert back by `recordSeg_iff` |
| 4: the unfolding ledger | **5 of 173** | rows 407 (with `recordRun_zero`), 441, 444 (`Cfg.mapState_state`), 465 (`Cfg.mapState_workTapePos` in the helper) and 1579 (`Cfg.mapState_workTapePos`). REPORT lists every other row as pending with its published lemma |

**Seal evidence** (`scripts/mkseal_file.py`, `scripts/run_seals.sh`, `scripts/sealcmp.py`;
`seals/`):
- **`Segment` and `HeadBox`, file-wide, at the head:** 0 errors (`seals/head-SegBox.out`). The
  new layer is read only through `segment_iff`, `headBox_iff` and the `Segment.*` lemmas; no
  projection or anonymous constructor reaches into it.
- **Each of the ledger's 20 non-abbreviation definitions, sealed file-wide one at a time, at
  base and head** (first error per tactic block, mapped to its declaration):

  | Definition | Base sites | Head sites | Gone at head | New at head |
  |---|---:|---:|---|---|
  | `Cfg.mapState` | 28 | 27 | base line 465 (`recordRun_tagged`, the ledger's implicit row) | none |
  | `MultiTapeTM.runFrom` | 16 | 15 | base line 407 (`recordRun_zero`, deleted) | none |
  | `Cfg.liftSymbols` | 20 | 20 | — | none |
  | `embedEmitCfg` | 12 | 12 | — | none |
  | `fieldOffset` | 7 | 7 | — | none |
  | `Action.apply` | 6 | 6 | — | none |
  | `roundOrbit` | 3 | 3 | — | none |
  | `FinTM.bufferTape`, `Cfg.inputSymbol`, `incFixed`, `scanKeep`, `scanFold`, `counterWord`, `Cfg.init` | 1 each | 1 each | — | none |
  | `decFixed`, `moveInputPos`, `fieldsTape`, `MultiTapeTM.step`, `MultiTapeTM.outputSymbol`, `Cfg.workTapeSymbols` | 0 | 0 | — | none |

  Head lines are mapped to base lines through the file alignment; every head error lies on a
  base error line (`seal-compare-lines.txt`, per declaration in `seal-compare.txt`). The base
  counts reproduce the ledger's implicit rows (`runFrom` 16, `liftSymbols` 20, `embedEmitCfg` 12,
  `fieldOffset` 7, `Action.apply` 6, …); `Cfg.mapState` gives 28 lines against the ledger's 26
  (the ledger is a lower bound). So the swap introduced no definitional unfolding and removed
  the two the kit carried.
- **Explicit sites** (definition names in `simp`/`rw`/`unfold` lists, comment-stripped,
  `scripts/explicit_sites.py`): base **76**, exactly the ledger's explicit count; head **73**. The
  three removed are `record_tag_ne` (2) and `recordStep_phase_run` (1), all `Cfg.mapState`. No
  new explicit site was added (`explicit-sites.txt`).

## (d) Escalations

None raised. REPORT states that no missing-API obstruction was met in the delivered portion, and
the brief's API (#118's three rounds, MIG-12's commit) lists a published lemma for every ledger
row. Nothing to probe.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 23 | Worker's before | byte-equal to `audits/logs/mig12-fill-screen-base.txt` minus comments (870 / 437 / 132,126) | `screen-compare-worker.txt` |
| 24 | Worker's after | 870 / 435 / 131,544; `pairdiff`: 0 new; 2 gone, the directed pair `recordRun_trans` ⇄ `Segment.trans` (100% / 99%), the copy this swap exists to remove | `screen-compare-worker.txt` |
| 25 | Mine, after (head, the 12-file population) | `declarations screened: 870; copy pairs …: 435; reproduced text: 131,544 chars` (exit 0, 525 s). **Byte-equal to the worker's `screen-after.txt`.** Against the issued base log: 0 new; gone the two `recordRun_trans` ⇄ `Segment.trans` pairs. No pair names a new declaration. No in-file pair was removed (phase 1 rewrote no phase proof) | `screen-after.txt`, `pairdiff-mine.txt` |
| 26 | Lint, `TuringMachine/Build` | `0 FAIL, 32 WARN over 37 files` at base and head; only `CfgRecord`'s size lines change | `lint-build-*.out` |
| 27 | Lint, `TuringMachine` | `0 FAIL, 67 WARN over 79 files` at both | `lint-tm-*.out` |
| 28 | Docstrings | the 5 new privates have docstrings; none needs a sketch (all under policy §3's ~20 lines) | `worker.diff` |

## (f) Landability on the stack top (`5333b29b`)

- **The owned file is unchanged base → stack top** (blob `08fb047f` at both). Both patches apply
  cleanly there, giving the head blob `1c9d198f` (`patch-at-tip.txt`).
- **Upstream** (28 modules with the new import, the same at head and stack top). Five changed in
  the stack: `Build/Convention`, `Build/CounterLoop`, `CodeParser`, `Encoding`, `Simulation`. All
  changes are additions only (declfreeze in the B5a review's `upstream-changes.txt`; same files).
- **Elaboration at the stack top** against `oleans-lx2`: exit 0, no error, no warning
  (`elab-tipd-lx2.out`).
- **Replay closure: 52 modules** (`CfgRecord` plus 51 downstream; `mkdownmulti.py`). The set and
  order are the same at base, head and stack top. The set equals the brief's
  `replay-closure.txt`; the order differs only among the `Logspace` modules
  (`closure-*.txt`, `closure-vs-brief.txt`). It spans `Build/RecordTable`, the `SpaceComplexity`
  codec, `ExpBFS`, `SavitchARM`, the Immerman–Szelepcsényi and `PathHard` chains, `WindowRun`,
  `WindowClock`, `ClassPSPACE/TQBF*`, and the `SpaceComplexity` and `TuringMachine` facades. The
  only module of the 52 that the stack touches is the `TuringMachine` facade.
- **Why it must be replayed.** The private changes cannot reach downstream statements, but the
  new import does: every one of the 52 modules now transitively imports the contract facade
  (simp sets, instances, names). The worker's sweep shows all 52 passing with the base's sorry
  set at the base; at the stack top it must be replayed into a copy of `oleans-lx2`. Expected:
  `CfgRecord` 0 warnings, and the closure's sorry warnings unchanged.

## Environment (REPORT; brief)

- **Startup.** Shim as authorized, after "failed to locate application"; `TAR_OPTIONS` and a
  task-private `MATHLIB_CACHE_DIR` for the cache.
- **Interruptions.**
  - Execution-service disconnects at bootstrap modules 134 and 186 and at final module 91, and
    a lost control channel during the final replay. Each resumed at the interrupted module.
  - An OOM kill (exit 137) at `CfgRecord` under an 8 GiB limit, while checks overlapped; they
    were serialized afterwards.
- **Cache handling.** Duplicate oleans were hardlinked and 880 byte-identical dependency oleans
  shared (cache storage only).
- **Effect.** None on the Lean result; my elaboration takes 2.4 GB alone.
- **For the addendum.** The memory headroom note (one Lean at a time for this file) and the
  free-disk precheck recommended after G4 cont1 apply here too.

## (g) Recommendation

**Not yet clear to merge**: no landing PR is open, and D1 decides whether one should be.

**D1 (decision for the user): land phase 1 now, or fold it into the continuation.**
- **Land now** (a maintainer PR cherry-picking `61c25b24` and `41d31d09`):
  - correct, admission-free and freeze-clean;
  - removes the 100% copy pair;
  - costs a 52-module replay into `oleans-lx2`, for +8 lines;
  - the continuation would then branch after it.
- **Fold (my recommendation):**
  - do not land separately;
  - continuation 1's brief prescribes these two commits, verified here, as its first commits
    (as cont5 did with the factoring patch), and its replay covers both;
  - the 52-module replay is paid once, when the phase lemmas are re-proved over the contracts;
  - nothing else is waiting on phase 1 alone: `WindowClock` and `RecordTable` see only public
    statements.
- **Either way:**
  - fix M2 by a flagged "Migration appendix (MIG-12)" on `exists_recordStepTM` and
    `exists_recordEqTM` (the retired names in their docstrings), or by maintainer wording when
    the module header's status text is updated;
  - if landing now, the PR body should say that phases 2–4 are pending.

**MIG-12 continuation 1 should:**
1. **Start from `41d31d09`** (fold) or from the landing commit.
2. **Phase 2, smallest first, keeping the file elaborating after each lemma:**
   `recordStep_halt_run`, `recordStep_state_run`, `recordStep_copyback_run`, …
   (`recordrun-uses.tsv` by size).
   - Read each row through its contract (`C.segment` into `RecordSeg` by `Segment.mono` with
     `record_headBox_mono`, `C.post`'s field equations), not `_run_ofCfg`.
   - Lift into the host by `phaseHostTM_run`, or `Contract.inPhase` with `Cfg.bindState_*`.
   - Keep the counter-loop exception (`recordStep_save_run`) on `counterLoopTM_run_escape`.
3. **Phase 4 alongside**, row by row from REPORT's table. The seal comparison above is a ready
   self-check: per definition, the head's first-error set must shrink to empty.
4. **Phase 3** last, and report the line delta against the −1.6k to −2.1k estimate.
5. **Inputs to keep:**
   - the screen base becomes this review's after-screen (435 pairs);
   - the 83-entry sorry set;
   - the 52-module closure;
   - the 227-name probe.
