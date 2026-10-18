# §12.8 fill, stream C, continuation 1 (partial; the record step): integration record

Brief: `briefs/s128-fill-C-cont.md` (ancestor `8e9a9b7e`). Delivery:
`infra_local/fill-s128-C-cont.zip`, agent commit `89b617b4` on base `4aafe9e4`. The agent's
report is `audits/s12-8-fill-agent-reports/C-cont-1-REPORT.md`. The patch was applied at the
campaign tip `fc999a8b` as `5a460237`. `CfgRecord.lean` is unchanged between base and tip,
since only audit files changed in between.

## Result

**Partial, 0/1.** `Turing.exists_recordStepTM` is not proved; its body ends in the one
`sorry` of the file. This is a continuation under ground rule 9, with no escalation and no
admitted helper.

**What is built and proved:**
- **The machine:** one `phaseHostTM` instance on the four-tape bank (record 0, B 1, Cs 2,
  D 3), `recordStepMachine`, with its stage, data and phase families and all R8 redirects.
  The only hand tables are the permitted Probe, Save and Read, each with its gap sentence.
- **48 named private declarations and 3 private instances, all proved:**
  - the width-one/empty-input test;
  - fixed-width carry and borrow, the complement value, and the saved digits;
  - the exact outward-move window equivalence;
  - the single-use R1 restriction, with an all-prefix transport wrapper;
  - the native-table frame;
  - Probe, Save and Read runs, and the save loop through `counterLoopTM_run_escape`;
  - the position and tape folds;
  - the F1 clamp;
  - the mark write and shift identities;
  - the full tape-word rewrite to `Action.apply`'s field.
- The first read segment (`recordStep_state_run`) is instantiated inside the target body.

The report's five-step frontier lists what is open: the read run R1–R6, the native cycle I0–I9,
dispatch and rewrite A0–A5, and the common ledger. A second continuation brief issues with
this PR.

## Verification (maintainer)

- **Integrity.** All 22 `SHA256SUMS` entries are OK. The zip has no C file and no script.
- **Integration.** `git am -3` applied cleanly, keeping the agent's authorship. The file
  matches the delivered snapshot byte for byte.
- **Freeze** (`audits/logs/s12-8-fill-C-cont-1-freeze.log`).
  - No statement changed. No public was added or removed. The tool's "public added: adds" is
    a docstring line beginning "lemma adds one dispatch", not a declaration.
  - The only body change is the target's.
  - 48 privates added; no existing private changed.
  - Imports unchanged.
  - The only `sorry` among the added lines is the target's.
- **Duplication.** The screens are byte-identical to the agent's:
  - main screen (`…-screen-after.txt`, base `s128-fill-C-cont-screen-base.txt`): 768 → 810
    declarations, 689 → 690 pairs;
  - with `Primitives` (`…-screen-after-prim.txt`): 988 → 1,030 declarations, 1,363 → 1,364
    pairs.

  The one new pair is in-file: `recordStep_probe_run` ← `recordStep_read_run` (69%). These are
  two different permitted native tables, and their one-step cases share the public action and
  the cut `u < 1`; the report justifies the pair. There is no cross-file pair (nothing against
  `InputCall`, and nothing against `Primitives`' `emitterP2_frame`). **New copies: none.**
- **Lint** (`…-stylelint.log`): 0 FAIL, 7 WARN over `TuringMachine/Build`, all size warnings.
- **Size:** `CfgRecord.lean` 1,289 → 2,409 lines. Brief ground rule 8 waives size, and file
  size alone is not a driver (user, 2026-10-11).
- **Replay** (`…-replay.log`). 4 modules at `5a460237` into a tip-consistent snapshot; the user
  ran it. **0 errors.** 5 sorry warnings: `CfgRecord` 1 (the target) and `TQBF` 4.
- **Axioms and admission walk** (`…-axioms.log`). All 15 `CfgRecord` publics are within the
  standard triple, except `exists_recordStepTM`, which prints `sorryAx`. The walk gives:
  - `exists_recordStepTM` rests only on itself;
  - `exists_recordEqTM` and `exists_recordTestTM` are admission-free.

## Disposition

This partial goes in by PR. The second continuation brief, `briefs/s128-fill-C-cont2.md`,
resumes at the report's frontier step 2. The §12.8 fill gate for streams A–C runs when the
step row completes.
