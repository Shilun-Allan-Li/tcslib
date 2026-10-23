# External audit pack — C1, UN continuation 1: the universal NDTM's setup (the UN landing, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the timed universal NDTM behind the
nondeterministic time hierarchy, [AB09, Theorem 3.2, Exercise 2.6]). The fill brief UN
continuation 1 (`campaign/fills/c1/briefs/c1-fill-universal-cont1.md`) targets
`Turing.exists_timed_universal_NDTM` (`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`):
the universal NDTM, through an eight-phase setup machine before the guess. It was delivered complete
as item 2 of megafill A on 2026-10-22 (`fill-c1-universal-cont1.zip`, SHA-256
`27ff57c319c2a7b6906ba3454de73b285878f00d996128aa49cbb0c33cdbdd69`), proved modulo exactly the
interpreter core `Turing.exists_ndInterpreterCore` (#151, gate 66). The worker's report is
`campaign/fills/c1/reports/universal-cont1-REPORT.md`, with the session report
`campaign/fills/megafill/reports/megafill-a-REPORT.md`. The maintainer's review is
`campaign/fills/c1/reviews/universal-cont1/REVIEW.md` ("complete; land with edits").

**The landing:** three commits, prepared on a local branch on #153's head `ac5ce7bc` (#153 is the
input-rewind API, gate 65; the landing needs it). The PR opens after #153 merges, with these three
commits on the campaign branch. Their content is fixed and is what this gate audits
(`campaign/fills/c1/evidence/c1-universal-cont1-landing/patches/`):
- `9031f1cf`, the delivery squashed to the owned file, with the worker's authorship kept. It is
  `git diff 6cfee544..d72ed65f` of the owned file (blob `8514e6db`); the delivered `evidence/`
  tree stays out of the library;
- `34568b28`, the review's landing edits (blob `958751e1`), all ruled by the user (2026-10-22):
  - A1 (F1): the decider's frozen docstring, which the overlay had reverted, is restored, with its
    clause updated;
  - A2–A4 (F5): the status text; the target's docstring gets an `**Implementation.**` paragraph
    in place of its fill-obligations sentence; the home's header;
  - A5–A7 (F5): three proof sketches;
  - B1–B3 (F2): three `simp only` repairs, so the sealed and unsealed runs agree;
  - C (F6): unused `simp` arguments and no-op `push_cast`s dropped;
- `3ed7b854`, the re-point (the user's ruling: an API PR first, then this landing re-points to it;
  the ledger's IR-1). The setup's last phase is `Turing.inputRewindTM`, run through
  `inputRewindTM_run`. The private `un_inRewTM`, `un_inRew_run` (with A7's sketch) and
  `un_mapState_comp` are removed, and `un_step'` collapses its tag through `Cfg.mapState_mapState`.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target proved** | `Turing.exists_timed_universal_NDTM`, modulo `Turing.exists_ndInterpreterCore` only; its body is `exact un_universal_of_setup c un_setup` |
| **Privates** | 0 → 11 at the landing's head: the overlay's `un_universal_of_setup` and the delivery's 13 new `un_` privates, less the re-point's three |
| **Frozen** | every public statement; 5 → 5 public declarations. The docstrings that change: the decider's, restored (A1); the target's, given the `**Implementation.**` paragraph (A3) |
| **The re-point** | 14 → 11 privates; bodies changed in `un_setup` and `un_step'` only (`campaign/fills/c1/evidence/c1-universal-cont1-landing/freeze-vs-edits.txt`) |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement: for every effective
   nondeterministic scheme, a universal NDTM with the stated linear overhead? Check the setup
   machine's budget `CP = 7|α| + 130` and the constant `C = CP + CR + 13`, and that no `|x|` term
   enters the setup's time. Check the boundaries: the empty code, the empty input, `t = 0`.
2. **Admission.** The target's `sorryAx` reaches it only through `exists_ndInterpreterCore`;
   `un_setup` is on the standard three (the review, out/20). When #151 lands, the target's chain
   changes accordingly.
3. **Rule 10.** The review's seal: 36 definitions, with and without the four `@[simp]` definitions
   erased; the body is clean and its 80 controls fail sealed and pass unsealed. On the re-pointed
   file the maintainer ran the same seal plus `Turing.inputRewindTM` (37 definitions, the simp
   erasure, 41 controls at the top and the end). The body has 0 errors and all 82 controls fail;
   unsealed, they close. Does any step still close only because another file's definition reduces
   or is `@[simp]`?
4. **The re-point.** Is `inputRewindTM_run`'s use exact? Check phase 8's run, exit state and cut,
   the composite's state type, `hfin`, and `un_step'`'s collapse. Does anything else change?
5. **The route refinements (the review's F4, accepted by the user).** The guided bank erase (a
   second private leaf); the input rewind, now the public API's. Are both sound and within the
   brief?
6. **Duplication.**
   - The review's screen: 603 → 616 declarations, 450 → 454 pairs, 4 new, none ≥ 90%. Its two
     cross-file pairs (F3) are removed by the re-point.
   - The landing's screen (the brief's 11 files plus `Build/InputRewind`): 617 declarations, 454
     pairs. Against the review's, 4 are gone: F3's two, `xr_E_initCfg` ← `un_mapState_comp`, and
     the in-file `un_setup` → `un_mapState_comp`. 4 are new: #153's three, which gate 65 covers,
     and `un_setup` → `Cfg.mapState_mapState` (88%). That last one is `hstart`'s field-by-field
     proof of the start configuration through seven relabelings, the old 87% in-file pair now
     pointing at the API. **The user accepted it as an idiom pair (2026-10-23).** Is that reading
     right?
7. **The text.** A1–A7 and the commit subjects: accurate and public-facing?
8. **Records.** The review's F7 (seal and axiom logs older than the last Lean commits, no shipped
   seal source, no checkpoints, no shared logs, a top-level `evidence/` tree): any correctness gap?

## Repository-side attestations (verify or challenge)

- **Elaboration:**
  - the review: the delivered file and the edited file (`958751e1`) have 0 errors and only
    `ntime_hierarchy`'s sorry warning, against `oleans-lg4c2` and `oleans-lu2sc1`;
  - the maintainer, on the re-pointed file: the same, checked as one file after the new module's
    text, with imports merged and against `oleans-lu2sc1`, because no snapshot yet has #153's
    module (`campaign/fills/c1/evidence/c1-universal-cont1-landing/elab-UNCat.out`, `UNCat.lean.txt`).
- **Probe** (the review): 95/95, at the base and the tip and in-module.
- **Lint:** `Diagonalization` 0 FAIL, 2 WARN, as at review; no line over 100 characters.
- **The sweep** (the worker): 75 modules, 26 → 25 sorry warnings.
- **Replay:** after #149 and #153 merge, the PR's closure (`Diagonalization/NTimeHierarchy`, the
  `Diagonalization` facade) replays from the latest merged-tree snapshot. **Pending:** by the
  user's ruling (2026-10-23) this gate is dispatched before the replay, which is recorded when it
  passes. The PR is clear to merge only when both have passed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/68-c1-universal-cont1-fill/findings.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `c1-universal-cont1-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
