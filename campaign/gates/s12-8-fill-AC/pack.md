# External audit pack — §12.8 fill gate, streams A–C: the configuration-record library rows (24 targets)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). §12.8 is the machine
library's rich-alphabet layer for configuration-graph walkers (`machine-library-design.md`
§12.8, §12.8a): the rows that S1b's breadth-first simulation, Savitch's recursion, PATH, the
space hierarchy and TQBF ∈ PSPACE cite. Its statement gate closed at round 2 with every
contract true as stated (`audits/s12-8-statements-r2-findings.md`; round 1
`audits/s12-8-statements-findings.md`; resolutions `audits/s12-8-statements-resolutions.md`).
Stream D (R8.0b, the generalized counter loop) had its own gate, closed at round 2. **This gate
covers streams A–C:**

| Stream | Owned files | Targets |
|---|---|---|
| **A** | `Build/Catalog.lean` (Part 3), `Build/Seam.lean` | 13: `fieldsTape_field`, the five `scanResult_*` identities, `scanTM_run_ofCfg`, `compareTM_run_ofCfg`, the four seeks (`skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM` `_run_ofCfg`), `seamCompTM₂_run_ofCfg` |
| **B** | `Build/Scan.lean` | 4: `writeConstTM_run_ofCfg`, `writeAdvTM_run_ofCfg`, `inputCopyTM_run_ofCfg`, `inputFoldTM_run_ofCfg` |
| **C** | `Build/CfgRecord.lean`, `Build/InputCall.lean` | 7: `cfgRecord_inj`, `recordValid_iff`, `exists_recordEqTM`, `exists_recordTestTM`, `exists_recordStepTM` (R8.7, the record step), `FinTM.exists_inputCallTM` (R8.5e), `exists_inputSeekTM` |

Six deliveries, each integrated by `git am -3` with Codex authorship (briefs at ancestor
`182e6f44`, after the pre-issue shared layers #32 and #33):

| Delivery | Brief | Integrated | Result |
|---|---|---|---|
| A | `briefs/s128-fill-A.md` | `3e856480`, PR #42 | 13/13 |
| B | `briefs/s128-fill-B.md` | `6c525fe8`, PR #41 | 4/4 |
| C | `briefs/s128-fill-C.md` | `25147e7a`, PR #41 | 6/7 |
| C, continuation 1 | `briefs/s128-fill-C-cont.md` | `5a460237`, PR #47 | the record-step machine and 48 components |
| C, continuation 2 | `briefs/s128-fill-C-cont2.md` | `774ee48e`, PR #49 | the full read, the halted branch, the native segments I0–I5 |
| C, continuation 3 | `briefs/s128-fill-C-cont3.md` | `14d1a383`, PR from `integrate/fills-4` | **the record step: 7/7** |

**Every proof is kernel-checked**; the replay and axiom evidence is below. All 24 targets now
print within `[propext, Classical.choice, Quot.sound]`. Fill gates close on zero blockers and
zero majors (`workflow.md` §4), and the duplication rule (`audits/TEMPLATE.md`, failure mode 5)
is in force. The standards are attached.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target bodies, `sorry` → proof** | all 24 |
| **Authorized swaps** (stream A) | the bodies of `compareTM_run` and `compareTM_spaceUsedByTape`; the four in-place compare replacements `catalog_compare_stop` (types only), `catalogCompareF`, `catalogCompareR`, `catalog_compare_trace` |
| **Privates added** | `Catalog` 12, `Seam` 0, `Scan` 15, `CfgRecord` 99, `InputCall` 9 |
| **Hand-built tables** (stream C's rule 10) | exactly three, in the record step: `Probe`, `Save`, `Read`, each with its gap sentence ("no public native-input-head primitive") |
| **Imports** | unchanged in all five files |
| **Docstrings** | flagged appendices where a route was refined; C's three continuation appendices are kept as history; status labels now "proved" |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached bases (at `182e6f44`), the head and the
   cumulative patch (`audits/evidence/s12-8/fill-gate/`; computed at `b0e922ab`, and the files are
   unchanged at the final head):
   - every statement is unchanged, and every landed definition and result (the carrier
     `Cfg.InWindow`, `RecSym`, `binDigits`, `posWidth`, `cfgRecord`, `RecordValid`, `RecordAt`;
     the pre-issue layer);
   - the only changed bodies are the 24 targets and stream A's two swaps;
   - the only changed privates are A's four compare replacements;
   - the imports are unchanged.
2. **Stream A's routes.** One shared structural `mealyRun_induction` for the `scanResult_*`
   identities. `scanTM_run_ofCfg` is one `catalog_trace_run` instance for both passes. The
   compare trace is generalized in place, with no surviving canonical twin. The four seeks go
   through one shared pass lemma. `seamCompTM₂_run_ofCfg` needs no new induction.
3. **Stream B's routes.** Three Scan contracts are instances of the public `catalog_trace_run`.
   The cyclic advancing writer uses the one allowed forward induction and shares a write step.
4. **Stream C's routes and the record step's obligations** (statement gate round-2 note 3,
   round-1 note 28):
   - **one** `phaseHostTM` instance (`recordStepMachine`) on the four-tape bank, and **one**
     single-use R1 restriction (`recordStep_restrict`), with no copy of Primitives'
     `emitterP2_frame`;
   - the native position saved in binary and restored exactly; seek, read, restore;
   - the position field clamped at `0` and `|x| + 1`;
   - an outward work-head move rejected **before** anything is written;
   - the fixed-length record rewritten field by field to `cfgRecord s (M.step c) (upd τ …)`;
   - every scratch tape globally blank at the end; the head-radius clause `C·(L + 1)`, with time
     `C·(L + |x| + 1)` at the coefficient `200·(k + 3)·(Cseek + 1)`;
   - the halted-source and empty-input cases; `|x| = 0` detected from the one-digit width.
5. **The statement gate's conventions:** verdicts intercepted at every sub-module's exit
   (round-2 note 7); R1 isolation of the dedicated digit tapes (notes 31–32); the input call
   time-only (note 8); no termination hypothesis (round-1 note 35).
6. **Duplication** (failure mode 5).
   - Each delivery's screens are recorded; the attached union screen covers all 13 population
     files at the head.
   - No delivery introduced a cross-file pair involving its owned files.
   - **Stream C's clear-phase family.** Continuations 2 and 3 add 18 in-file pairs at 51–86%,
     none at 90%. Most are among short phase lemmas that clear a scratch tape and then dispatch:
     `recordStep_empty_run`, `_reject_run`, `_halt_run`, `_copyback_run`, `_position_run`,
     `_restore_native`. Each instantiates the shared `recordStep_clear_snapshot`,
     `recordStep_clear_heads` and `recordStep_phase_run`. The rest are snapshot specializations
     and traversal wiring (`recordStep_map_snapshot`, `_read_prefix`, `_read_fields` ←
     `_write_back`). Each pair is justified in its report. The maintainer notes the family as a candidate
     for one in-file factoring (a generic clear-then-dispatch phase lemma). Rule whether any
     pair must be factored now.
   - All population files and the screen script are attached for a rerun.
7. **The hand-built tables.** Confirm that `Probe`, `Save` and `Read` are the only hand tables,
   that each is a few states over `inputMoveAction`, and that each carries its gap sentence. The
   requested public native-input-head primitive is an open 12.2c candidate.
8. **Documentation.** Check the appendices, the status labels and each new private's sketch
   against the delivered proofs.
9. **Size.** `Catalog.lean` (12,732 lines) and `CfgRecord.lean` (2,409 → 5,255 across the
   continuations) are large. The briefs waive size, and file size alone is not a driver (user,
   2026-10-11). Catalog's per-theme split is 12.2c tranche T3. Say whether you disagree.
10. Report anything else the fill or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** Every delivery's `SHA256SUMS` was all OK; the manifests are attached.
  The deliveries' environment shims and agent scripts were never compiled or run, and nothing
  references them. These are maintainer attestations.
* **Freeze:** per delivery, `audits/logs/s12-8-fill-*-freeze.log`; cumulative,
  `audits/evidence/s12-8/fill-gate/freeze-cumulative.log`.
* **Replays** (user-run, fresh `.oleans` into tip-consistent snapshots): one per delivery; the
  combined tree after R8.0b and the wave-1 statements (`audits/logs/fills-3-combined-replay.log`);
  and the final head (`audits/logs/fills-4-replay.log`): 11 modules, **0 errors**, `CfgRecord` 0 sorry
  warnings. Two top-ups (`audits/logs/fills-4-replay-topup.log`, 15 modules, and `-topup2.log`, 2)
  cover the files merged afterwards, outside A–C's closure: 0 errors.
* **Axioms** (`audits/logs/s12-8-fill-AC-axioms.log`; probe
  `audits/evidence/s12-8/fill-gate/S128FillACAxioms.lean.txt`, at the head):
  - all 24 targets print within `[propext, Classical.choice, Quot.sound]`;
  - all 24 admission walks are empty;
  - the censuses of every private constant of the five files (1,559, 21, 73, 1,059 and 50)
    find no `sorryAx`.

  Each delivery's own axiom log is attached as well.
* **Pre-ship probes:** `audits/evidence/s12-8/S128FillCProbe.lean.txt`, rerun at each C issue
  tree.
* **Lint:** 0 FAIL over `TuringMachine/Build`; the warnings are all file-size ones.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-8-fill-AC-findings.md`. The gate closes when it has zero blockers and zero majors;
§12.8 is then complete.
