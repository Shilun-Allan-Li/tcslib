# §12.8 fill, streams B and C (wave 1): integration record

Briefs `briefs/s128-fill-B.md` and `briefs/s128-fill-C.md` (ancestor `182e6f44`). Deliveries
`infra_local/fill-s128-{B,C}.zip`, agent commits `bda5a46f` (B) and `fde80b42` (C), both on
base `37ab6091`. Agent reports: `audits/s12-8-fill-agent-reports/{B,C}-REPORT.md`.

The two streams own disjoint files, so this branch holds both deliveries. B was applied at the
campaign tip `aed5b4ff` as `6c525fe8`, and C as `25147e7a`, merged with a merge commit. The
replays ran at those two commits, and the owned files here are byte-identical to them.

Stream D (R8.0b) is integrated separately, on `integrate/s128-D`, because its brief requires
its own R8.0b audit gate before merge. Its record is `audits/s12-8-fill-D-integration.md` on
that branch. Stream A has not yet been delivered.

## Result

| Stream | Targets | Status |
|---|---|---|
| **B** (Scan) | `writeConstTM_run_ofCfg`, `writeAdvTM_run_ofCfg`, `inputCopyTM_run_ofCfg`, `inputFoldTM_run_ofCfg` | **4/4 proved**, standard axioms; no admitted helper |
| **C** (CfgRecord, InputCall) | `cfgRecord_inj`, `recordValid_iff`, `exists_inputSeekTM` | proved, standard axioms |
| | `FinTM.exists_inputCallTM` | proved modulo stream B's `inputCopyTM_run_ofCfg`, **so admission-free on this branch** |
| | `exists_recordTestTM`, `exists_recordEqTM` | proved modulo stream A's rows (the brief's permitted set) |
| | `exists_recordStepTM` | not filled; original `sorry` kept (continuation, ground rule 9) |

C is a partial delivery, 6/7. Neither stream has an admitted helper.

**B's routes.**
- Three of the four contracts are instances of the public two-pass trace `catalog_trace_run`.
- The cyclic advancing writer has the one forward induction the brief allows: its exit state
  is also its entry, so the trace's stationary-exit hypothesis is unavailable.
- The three writing rows share one write step, `scan_write_step`, which cites
  `step_of_tapeAction_write` and `catalog_write_take`.

**C's routes.**
- The test and equality rows are one public `phaseHostTM` instance each, invoking
  `phaseHostTM_run` per phase.
- The seek is the prescribed copy → rewind → countdown → clear composition, through
  `FinTM.rewind_heads` and `counter_cfg_eq`.
- The two small native-input-head tables are the ones the brief permits.

## Verification (maintainer)

- **Integrity.** All `SHA256SUMS` entries are OK (B 19, C 21). B's C file
  (`evidence/lean-self-path.c`, an `LD_PRELOAD` shim for the agent's environment) is excluded:
  it was never compiled or run, and neither patch nor any source references it. C's zip has no
  C file and no script.
- **Integration.** Each one-patch series applied cleanly with `git am -3` at `aed5b4ff`,
  keeping the agent's authorship. The owned files are unchanged between `37ab6091` and the
  tip, and each matches its delivered snapshot byte for byte.
- **Freeze** (`audits/logs/s12-8-fill-{B,C}-freeze.log`, the maintainer's own check).
  - No statement changed. No public was added or removed. Bodies changed only at the filled
    targets (B four, C six).
  - Privates added: B 15 (the `scan*` families and the three trace instances); C 28 (19 in
    `CfgRecord`, 9 in `InputCall`), plus private phase instances. Both lists match the reports.
  - Imports are unchanged.
  - No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in
    the added lines.
  - Outside declarations, only flagged status text and C's flagged "Fill-C sketch appendix"
    changed.
- **Duplication.**
  - **B, main screen** (`audits/logs/s12-8-fill-B-screen-after.txt`, base
    `s12-8-fill-B-screen-base.txt`): 550 → 566 declarations, 415 → 421 pairs.
    - The only new cross-file pair is the brief's allowed `scanWriteCfg` ↔ `catalogCopyF`
      (55–56%), two framed-configuration definitions.
    - The four new in-file pairs (52–64%) are clause extraction from each row's own trace
      instance, each justified in the report.
  - **B, advisory screen** (`audits/logs/s12-8-fill-B-advisory-after.txt`): 283 → 299
    declarations, 230 → 234 pairs, the same four in-file pairs, no cross-file pair.
  - **C, main screen** (`audits/logs/s12-8-fill-C-screen-after.txt`, base
    `s128-fill-C-screen-before.txt`): 714 → 742 declarations, 680 → 682 pairs. The only new
    pair is `RecordEqIndex` ↔ `RecordTestIndex` (55–57%): constructor syntax of two different
    phase-index types.
  - **C, with `Primitives`** (`audits/logs/s12-8-fill-C-screen-after-prim.txt`): the same
    single new pair, and no pair against `emitterP2_frame`.
  - No pair disappeared in any run. **New copies: none.** No ledger change.
- **Lint** (`audits/logs/s12-8-fill-BC-stylelint.log`): 0 FAIL, 15 WARN over
  `TCSlib/Complexity/TuringMachine`, all size warnings. The one new warning is `CfgRecord`.
- **Sizes.**

  | File | Lines | Change |
  |---|---|---|
  | `Scan` | 666 | from 276 |
  | `CfgRecord` | 1,289 | from 346 |
  | `InputCall` | 534 | from 120 |

  `CfgRecord` crosses 1,000 lines. Justification: brief ground rule 8 forbids new files, and
  file size alone is not a driver (user, 2026-10-11).
- **Replays** (`audits/logs/s12-8-fill-{B,C}-replay.log`). Both cover the downstream closure
  of the changed files, run at `6c525fe8` and `25147e7a` into snapshots of a tip-consistent
  olean tree. The user ran them from the maintainer's command. **0 errors** in both.
  - B, 7 modules, 12 sorry warnings: `Scan` 0, `CounterLoop` 1, `InputCall` 2, `CfgRecord` 5,
    `TQBF` 4, both facades 0.
  - C, 5 modules, 5 sorry warnings: `InputCall` 0, `CfgRecord` 1 (`exists_recordStepTM`),
    `TQBF` 4, both facades 0.
  - The owned files' downstream depends only on their frozen statements, which are identical
    in both streams, so the two replays together cover this branch.
- **Axioms** (`audits/logs/s12-8-fill-{B,C}-axioms.log`; probes
  `audits/evidence/s12-8/S128Fill{B,C}Axioms.lean.txt`, every public declaration of the owned
  files). Read-only against each replay's tree.
  - B: all 9 publics are within `[propext, Classical.choice, Quot.sound]`.
  - C: 13 of 17 publics are within the standard triple. Exactly the four expected print
    `sorryAx`: the three modulo targets and `exists_recordStepTM`.
- **Admission walk** (`audits/logs/s12-8-fill-C-admissions.log`; probe
  `audits/evidence/s12-8/S128FillCAdmissionWalk.lean.txt`). This lists the constants in each
  target's closure whose own type or value mentions `sorryAx`, and matches C's ledger exactly:
  - `exists_inputCallTM`: `inputCopyTM_run_ofCfg` only (B proves it);
  - `exists_recordTestTM`: `fieldsTape_field`, `scanTM_run_ofCfg`, `scanResult_fold`,
    `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg` (all stream A);
  - `exists_recordEqTM`: `fieldsTape_field`, `compareTM_run_ofCfg`, `skipTM_run_ofCfg`,
    `skipBackTM_run_ofCfg` (all stream A);
  - `exists_recordStepTM`: itself.

## Notes for the follow-ups

- **C's request (recorded, not actioned).** A public native-input-head primitive would replace
  C's two permitted small hand tables (`inputSeekRewind`, `inputSeekStep`). This is a 12.2c
  candidate. The record-step continuation may use the brief's permitted Probe/Save/Read tables
  meanwhile.
- **C continuation.** A continuation brief for `exists_recordStepTM` follows, under route R8.
  It must not widen the permitted modulo set, the nine stream-A rows.

## Disposition

- This PR can merge now. The **§12.8 fill gate** for streams A–C runs once A is delivered and
  C's continuation completes, and covers this delivery. Stream D has its own R8.0b gate.
