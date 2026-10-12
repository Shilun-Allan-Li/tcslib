# §12.8 fill, stream C, continuation 2 (partial; the record step): integration record

Brief: `briefs/s128-fill-C-cont2.md` (ancestor `d71c389a`). Delivery:
`infra_local/fill-s128-C-cont2.zip`, agent commit `fcd3cacd` on base `d0b7761f`. The agent's
report is `audits/s12-8-fill-agent-reports/C-cont-2-REPORT.md`. The first continuation's
record is `audits/s12-8-fill-C-cont-integration.md`. The patch was applied at the campaign tip
`d0b7761f` as `774ee48e`.

## Result

**Partial, 0/1.** `Turing.exists_recordStepTM` is not proved. Its body keeps one `sorry`, in
the live-source branch. This is a continuation under ground rule 9:
- no escalation;
- no admitted helper;
- no correction to the machine definitions.

**What is now proved:**
- **The full read R1–R6**, `recordStep_read_all`: from the actual entry configuration to the
  exact source observations and tag. Both canonical digit copies are on B and D; the record,
  output and native position are unchanged; the work heads are restored. Time
  `≤ (10·(k + 3) + 17)·(L + 1)`, radius `L + 1`.
- **The halted-source branch, inside the target.** Both buffers are cleared and `yes` is
  reached. The record is unchanged (`step_of_halt`, `outputSymbol_of_halt`, `hupd`). The full
  cut, endpoint, time and radius hold with the coefficient `200·(k + 3)·(Cseek + 1)`.
- **Native segments, each separately composed in the one host:**
  - I0 (empty input; no native movement);
  - I1–I3 (fuel, probe, Save; `recordStep_prepare_native`);
  - I4–I5 (the recorded seek and Read; `recordStep_seek_read`);
  - the rejection cleanup N.
- **Rich transports:** the public seek on any selected two-tape digit bank, and Save on D.
  Both preserve every unselected rich frame cell and the output.

There are 20 new private declarations: 3 definitions and 17 theorems. The report's frontier
lists what is open:
- the concatenation of the live branch with I6–I9 (complement, decrement, restore, clear);
- the rewrite A0–A5;
- the endpoint and the common time and radius ledger.

The third continuation brief, `briefs/s128-fill-C-cont3.md`, issues with this PR.

## Verification (maintainer)

- **Integrity.** All 26 `SHA256SUMS` entries are OK. The zip has no C file and no script. Its
  `verification/` probes, one of which uses `run_cmd`, were read, not run; the maintainer's own
  probe replaces them.
- **Integration.** `git am -3` applied cleanly, keeping the agent's authorship. The file matches
  the delivered snapshot byte for byte (SHA-256 `8a16d847…`, as reported).
- **Freeze** (`audits/logs/s12-8-fill-C-cont-2-freeze.log`).
  - No statement changed, and no public was added or removed.
  - The only body change is the target's (authorized), together with its flagged
    "continuation 2 sketch appendix". The prior appendix's text is kept.
  - 20 privates added; no existing private changed. Imports unchanged (4).
  - The only `sorry` among the added lines is the target's.
- **Duplication.** The screens are byte-identical to the agent's:
  - main screen (`…-screen-after.txt`): 810 → 830 declarations, 690 → 698 pairs;
  - with `Primitives` (`…-screen-after-prim.txt`): 1,030 → 1,050 declarations,
    1,364 → 1,372 pairs.

  All eight new pairs are in-file, at 57–86%. The two highest are `recordStep_reject_run` ↔
  `recordStep_empty_run` (86%/85%): two short instantiations of the shared clear
  specialization and the host phase, for different stages and tapes. The agent factored their
  shared radius argument (`recordStep_clear_heads`) when they first screened at 90–91%. That
  leaves them below the brief's 90% factoring line, and the report justifies each pair. There
  is no cross-file pair. **New copies: none.**
- **Lint** (`…-stylelint.log`): 0 FAIL, 7 WARN over `TuringMachine/Build`, all size warnings.
- **Size:** `CfgRecord.lean` 2,409 → 3,786 lines (15 public / 87 private). Ground rule 8
  waives size, and file size alone is not a driver (user, 2026-10-11).
- **Replay** (`…-replay.log`, user-run): 4 modules at `774ee48e` into a tip-consistent
  snapshot. **0 errors.** 5 sorry warnings: `CfgRecord` 1 (the target) and `TQBF` 4.
- **Combined tree** (`audits/logs/fills-3-combined-replay.log`, user-run). The delivery was
  built without PR #38's generalized `CounterLoop`; its save loop cites
  `counterLoopTM_run_escape`. Since PR #43, `Build/RecordTable` imports `CfgRecord`. The
  13-module replay of `integrate/fills-3` gives **0 errors**:
  - `CfgRecord` 1 sorry warning;
  - the five wave-1 statement modules exactly their 26 sorried statements;
  - `CounterLoop` 0.
- **Axioms and admission walk** (`…-axioms.log`; probe
  `audits/evidence/s12-8/S128FillCCont2Axioms.lean.txt`), on both trees, with identical output.
  - All 15 `CfgRecord` publics print within the standard triple, except `exists_recordStepTM`,
    which prints `sorryAx`.
  - The walk gives `exists_recordStepTM` as resting only on itself; `exists_recordEqTM` and
    `exists_recordTestTM` are admission-free.
  - A census of all 818 private constants of `CfgRecord` finds none that uses `sorryAx`.

## Disposition

This partial goes in by PR. The third continuation brief resumes at the report's frontier
step 2, on the combined tree. The §12.8 fill gate for streams A–C runs when the step row
completes.
