# External audit pack — C1, R continuation 2: the interpreter core (PR #151, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the timed universal NDTM behind the
nondeterministic time hierarchy, [AB09, Theorem 3.2, Exercise 2.6]). The fill brief R
continuation 2 (`campaign/fills/c1/briefs/c1-fill-core-cont2.md`) targets
`Turing.exists_ndInterpreterCore` (`TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean`): the
interpreter core of the universal NDTM, a left-nested seam composite of twelve phases. It was
delivered complete as item 1 of megafill A on 2026-10-22 (`fill-c1-core-cont2.zip`, SHA-256
`4a2896a39cba455ef03997b8d5162c979569615f97f68a7087fe1feea159ce9b`), proved modulo exactly the
per-code replay canonizer `Turing.exists_replayCanonizer` (still sorried). The worker's report is
`campaign/fills/c1/reports/core-cont2-REPORT.md`, with the session report
`campaign/fills/megafill/reports/megafill-a-REPORT.md`. The maintainer's review is
`campaign/fills/c1/reviews/core-cont2/REVIEW.md` ("complete; land with the rule-10 fix").

**The head:** `lean/c1-core-cont2` at `f48ea176`, on the campaign branch at `86523ba5`. This
bundle's records are from a later records commit (stated in the bundle's README).
- 16 of the delivery's 19 commits, applied by `git am -3` restricted to the owned file, with the
  worker's authorship and subjects (the user's ruling). The delivery also committed its evidence
  logs to a repository-root `evidence/` tree, which stays out of the library. The owned file comes
  out as the delivered blob `7d1657b3`;
- `5825c7b6`, the maintainer's (the review's F1, the user's ruling): the review's four-hunk
  repair of six rule-10 sites. Four steps closed only by unfolding `MultiTapeTM.runFrom` in the
  rewind leaf's runs, and two only by unfolding `CodeNDTM.toFinNDTM` in the verdict's `if`; they now
  read those through published equations;
- `f48ea176`, the maintainer's, docstrings only: the module's contents line, the facade's line,
  and an `Implementation.` paragraph naming the core's twelve phases.

**One more commit at landing (the user's ruling, 2026-10-23).** If #153 (the input-rewind API,
gate 65) merges first, #151 re-points its private input-rewind leaf to the public one at landing.
The leaf is `ic_rewindLeafTM`, with `ic_rewind_scan` and `ic_rewind_leaf_run`; the ledger's IR-1
records `ic_rewind_scan` as re-proving the public `Turing.FinTM.rewind_scan`. The re-point is
`89bf6acb`, prepared on a local branch: #151's head, with #153 merged in locally to make the API
available, then the re-point. It is checked and is part of this gate:
`campaign/fills/c1/evidence/c1-core-cont2-leaf-repoint/`. Both rewind phases become
`Turing.inputRewindTM`, run through `inputRewindTM_run`, and the three privates are removed.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target proved** | `Turing.exists_ndInterpreterCore`, modulo `Turing.exists_replayCanonizer` only |
| **Privates added** (25, `ic_`; the base has none) | the overlay's 20 helpers verbatim, and 5 new: `ic_seam_step`, `ic_rewindLeafTM`, `ic_rewind_scan`, `ic_rewind_leaf_run`, `ic_install_phase` (`evidence/freeze-base-to-head.txt`) |
| **Frozen** | the target's statement and docstring; 3 → 3 public declarations, at source |
| **Code after the delivery** | exactly the review's repair (`evidence/code-identity.txt`: the delivered file plus `reviews/core-cont2/out/21-repairs.diff` equals the head, comments stripped) |
| **At landing** (if #153 is in) | the leaf re-point: 25 → 22 privates, the three leaf declarations removed; only the target's body changes; no statement changes |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement for every effective code and
   every input, with the constants chosen before the input, through the brief's twelve phases in
   the prescribed startup order? Check the time ledger
   `C = a + 43 + (CW + 2) + 50(L + 1) + 10` (`ic_time_ledger`) for both clauses, and the
   boundaries (the empty code, the empty input, `t = 0`).
2. **Admission.** The target depends on `[propext, sorryAx, Classical.choice, Quot.sound]`, with
   `sorryAx` reaching it only through `exists_replayCanonizer`
   (`evidence/elab-NDCodeSimulator-head-axioms.out`, against `oleans-lu2sc1`).
3. **Rule 10 (the review's F1, a major resolved by the repair).** Does any other step still close
   only because another file's definition reduces or is `@[simp]`? The review's seals S1 and S2
   (46 definitions; the four `@[simp]` ones erased in S2) are clean on the repaired file, and its
   50 controls fail sealed and pass unsealed.
4. **The re-point (prepared, applied at landing).** Is it exact? Check that
   `inputRewindTM_run`'s first two clauses are the old `ic_rewind_leaf_run`, with `start` and
   `done` for `0` and `2`. Check the seam chain's entry and exit states (`S₂`, `S₃`, `S₇`, `S₈`)
   and the composite state types `St₂` and `St₇`, and that no other proof changes. Its evidence:
   - the file elaborates with only the canonizer's sorry warning;
   - the review's seal plus `Turing.inputRewindTM` (47 definitions, the simp erasure):
     - with controls at the top only: the body has 0 errors and all 51 controls fail;
     - with controls at the top and the end: 100 errors, all on controls, where Lean's
       `maxErrors` cap stops; the last control is not reported;
   - unsealed, all 102 controls close;
   - freeze: 3 → 3 public, 25 → 22 private, only the target's body changed;
   - lint 0 FAIL;
   - screen: 6 pairs gone, 0 new (below).

   Do these establish the re-point?
5. **Duplication.**
   - The review's screen (the brief's population): 460 → 465 declarations, 118 → 120 pairs. Its
     one cross-file pair, `ic_rewind_leaf_run` → `iw_one` (69%), was accepted by the user as an
     idiom pair.
   - The re-point's screen (the brief's population plus `Simulation` and `Build/InputRewind`, at
     the local merge and after the re-point): 6 pairs gone and none new. Gone are that 69% pair,
     the IR-1 pair `ic_rewind_scan` → `rewind_scan` (51%), and the leaf's pairs with
     `inputRewindTM`.
   - In both screens, `exists_ndInterpreterCore` reproduces 85% of `Cfg.mapState_mapState`'s
     text. These are field-by-field rewrites through the relabeling's equations, the idiom the
     user accepted for UN's `hstart` (gate 68). Is that the right reading here?
6. **The text.** The contents line, the facade's line and the `Implementation.` paragraph:
   accurate and public-facing?
7. **Records.** The review's F4 (several REPORT statements wrong or stale) and F5 (evidence-only
   commits, kept out of the library): any correctness gap?

## Repository-side attestations (verify or challenge)

- **Elaboration and axioms:** the review: 0 errors at the base (`oleans-lg4c2`) and at the tip
  (`oleans-lu2sc1`), the canonizer's sorry warning only. The maintainer, at `f48ea176` against
  `oleans-lu2sc1`: the same, and the target on the axioms of item 2.
- **Probes** (the review): the brief's 220 checks and a 238-check extended probe, 0 errors.
- **Seal** (the review): item 3; `reviews/core-cont2/out/23*`, `24*`.
- **Lint:** the review's: 0 FAIL, the one new WARN the file's size. The re-point:
  `TuringMachine` 0 FAIL, 67 WARN over 83 files.
- **The census** (the worker): 38 → 37 sorry warnings over 118 modules, only the target's gone.
- **Replay:** the closure (`NDCodeSimulator`, `Diagonalization/NTimeHierarchy`, `Diagonalization`,
  the `TuringMachine` facade) overlaps #149's, so this PR merges after #149 and replays from the
  latest merged-tree snapshot. **Pending:** by the user's ruling (2026-10-23) this gate is
  dispatched before the replay, which is recorded when it passes. The PR is clear to merge only
  when both have passed. The branch merges cleanly with #149's head (`git merge-tree`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/66-c1-core-cont2-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `c1-core-cont2-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
