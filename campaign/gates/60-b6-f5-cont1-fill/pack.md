# External audit pack — B6, F5 continuation 1: the ruler device's call rows and host (PR #146, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, B6 (the space hierarchy, [AB09, §4.1.3, Theorem 4.8],
through the space-universal machine of Ex. 4.1). `TuringMachine/Build/InputDevice.lean` is host
H5 of the machine library: the input-device interface, the native device, and the bounded-prefix
ruler device. Its first fill round landed the restoring boundary test `Turing.exists_rulerTestTM`
(#133, gate 51). **Continuation 1** (`campaign/fills/b6/briefs/b6-fill-rulerdevice-cont1.md`), item
2 of megafill B (`campaign/fills/megafill/briefs/megafill-B.md`), was delivered complete on
2026-10-22: both remaining targets are proved, with no admission. The worker's report is
`campaign/fills/b6/reports/rulerdevice-cont1-REPORT.md`; the maintainer's review,
`campaign/fills/b6/reviews/rulerdevice-cont1/REVIEW.md` ("complete; land").

**The head:** `lean/b6-f5-cont1` at `8114e482`, on the campaign branch at `43d22595` (TCSlib =
`b7447492`'s, after #139 and #143):
- `b6c9e0c5`, `b26d53c9`: the worker's commits `8fa8598e`, `0f57ba49` (on the base `6cfee544`),
  cherry-picked from the verified bundle; they touch only the owned file;
- `8114e482`, the maintainer's, docstrings only: the module's status and main results, the
  `TuringMachine` facade's line, and an `**Implementation.**` paragraph after each target's frozen
  proof sketch, since the proofs take routes the sketches do not name (the review's F1; as #133
  did for the test).

## What changed (verify)

| Class | Declarations |
|---|---|
| **Targets proved** | `Turing.exists_rulerDeviceTM` (the call rows: read the virtual input cell, move the virtual input head) and `Turing.exists_rulerHostTM` (the ruler host: a positive finite block simulation of a native-input machine on the suffix input) |
| **Privates added** (32, `rd_`) | the call controller (`rd_callTM` and its phases, the one-step leaf over `Turing.inputMoveAction`, the dispatch), its run and the shared phase contracts; the host (`rd_hostTM`, its encoding, the paused test on the last tape, the block and the frames) |
| **Frozen** | every statement and docstring of the base, the three targets' included; the module's definitions (`inputCell`, `NativeAt`, `RulerAt`, `rulerHostCfg`) |
| **Size** | 525 → 1,294 lines; 15 public, 9 → 41 private (`evidence/land/landing-checks.txt`) |

## Brief for the auditor

1. **Faithfulness.** Do the two proofs establish the frozen statements for every argument, at
   their boundaries in particular: `ℓ = 1`, `z = [true]`, `y = []` at both positions; an empty
   payload at `p = |z| + 1`, where the virtual and physical right clamps coincide; the clamped
   right move at `i = |y| + 1`; a source that halts on a left move (no pause after a halting
   transition); zero bank tapes; an initially halted source? Is the host's `inj` a state map, not
   an injection, as the statement gate ruled?
2. **The call rows.** One phase host runs the boundary test, a one-step leaf (stationary for a
   read; for a move the clamped move, with a left move suppressed on `yes`) and a dispatch, in
   exactly `2ℓ + 5` steps, so `C = 4`. Are the read answers right (blank on `yes`, the native
   symbol on `no`), and the moves the virtual input's?
3. **The host.** A `Turing.Lockstep` over `Turing.rulerHostCfg` with the tag `c.inputPos = 0`: a
   block costs one step, or `2ℓ + 3` after a live left move from a cleared tag (the test on the
   last tape, through `Turing.embedEmitTM` and the guarded state transport), so `C = 3`. Do the
   intermediate frames, the exit cut, and the time and space ledgers hold as separate clauses, and
   are the bank's visited sets equal as claimed (`Turing.MultiTapeTM.mem_visitedByTapeHead_iff`)?
4. **Rule 10.** The review sealed 17 other-file definitions and erased two simp sets; its 38
   controls fail sealed and pass unsealed, and no other-file definition is among the 376
   rewrite arguments (`reviews/rulerdevice-cont1/out/`). Does any step still close only because
   another file's definition reduces? Rule 11 (no R3 row, no other file's private).
5. **The text.** Are the two `**Implementation.**` paragraphs accurate to the proofs, and the
   frozen sketches, now superseded in their route, still true as plans? The new docstrings: no
   campaign labels (the review notes three uses of "R1", registry nomenclature, and 11 privates
   without docstrings, left for the deferred public-facing pass).
6. **Duplication.** The screen: 720 → 741 declarations, 488 → 489 pairs; the one new pair is
   in-file at 79%, none cross-file. The known hazard `Build/VirtualInput` (Z1), the host pattern's
   model: is anything transcribed from it?
7. **A note for the consumers** (the review's O1): two read exits keep moving after `2ℓ + 5`;
   harmless where a seam redirects at the exit. Should the statement say so, or the consumers'
   briefs?

## Repository-side attestations (verify or challenge)

- **Elaboration** (the review): 0 errors, 0 warnings at the base (`oleans-lg4c2`) and at the tip.
  The maintainer, the landed head against `oleans-lg4c2`: 0 diagnostics
  (`evidence/land/elab-InputDevice-lg4c2.out`); the code identical to the delivered file with
  comments stripped (`evidence/land/landing-checks.txt`).
- **Axioms** (the review): all three targets on `[propext, Classical.choice, Quot.sound]`; no
  `sorryAx` in any closure; 56 prints, agreeing with the worker's 35 on every shared name.
- **Probes** (the review): the brief's 62 checks and the worker's 148, 0 errors, also against the
  delivered module.
- **Lint** (the landed head): `TuringMachine/Build` 0 FAIL, 32 WARN over 39 files; the new WARN is
  the file's size (`evidence/land/lint-build.txt`). No line over 100 characters.
- **The sweep** (the worker): 95 modules, 0 errors; sorry warnings 33 → 31, exactly the two
  targets.
- **Environment:** megafill B, under addendum v2.4 (one preflight and one narrowed cache fetch for
  the queue; Part 2's shim used, as authorized).
- **Replay:** ⟨REPLAY⟩

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/60-b6-f5-cont1-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `b6-f5-cont1-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
