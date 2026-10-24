# External audit pack — B6 F3, continuation 2: the configuration-count runner (the F3 landing, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, B6 (the space hierarchy's windowed runner, [AB09,
§4.1]). The fill brief F3 continuation 2 (`campaign/fills/b6/briefs/b6-fill-configclock-cont2.md`,
issued at the inputs commit `968d7b2b`) targets `Turing.exists_configWindowRunnerTM`
(`TCSlib/Complexity/SpaceComplexity/WindowClock.lean`): the windowed runner with a clock that
counts the configurations of the window. It was delivered complete on 2026-10-23
(`fill-b6-configclock-cont2.zip`, SHA-256
`076cea1a8f2b0bd2858ac22c1cd818f27e771c783d3c00c3186a2c81d19732e5`). The worker's report is
`campaign/fills/b6/reports/configclock-cont2-REPORT.md`; the maintainer's review is
`campaign/fills/b6/reviews/configclock-cont2/REVIEW.md` ("complete (1/1); land with two status
edits"), with its evidence (`out/`, `probe/`, `scripts/`).

**The landing:** PR on `lean/f3c2-landing` at `1911b1ca`, seven commits on the campaign branch at
`21d53053` (after #156). Their content is what this gate audits
(`campaign/fills/b6/evidence/b6-configclock-cont2-landing/patches/`):
- six commits, the delivery's format-patch series applied unchanged by `git am -3` (the worker's
  authorship and subjects kept, by the user's ruling of 2026-10-24); they reproduce the delivered
  file byte for byte (blob `71327d9d`), and each elaborates with only the target's sorry, the
  last with none;
- `1911b1ca`, the review's landing edits A1 and A2 (F1): the module's **Status** paragraph and
  its main-results entry say the runner is proved (blob `85de9ad5`). Text only.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target proved** | `Turing.exists_configWindowRunnerTM`, with no `sorryAx` |
| **Privates** | 11 → 66: 55 new `cw_` declarations; `cw_copy_constant` and `cw_clear_patch` restated (region (a) allows it); the other nine unchanged |
| **Frozen** | every public statement and docstring; 4 → 4 public declarations; imports unchanged. New public constants only of `workflow.md` §4's two kinds: the target's `_proof_` auxiliaries and the derived instances `instDecidableEqCw_Idx`, `instFintypeCw_Idx` |
| **Text** | the module's status paragraph and main-results entry (A1, A2) |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement? Check the constant
   `c = C₂ + |Q| + 8` and the statement's `C = (14c + 13) + 4c + 0 + 10 + C₂(c + 1) + c + 2`
   (the report's §6), the clock width `W = c · F ≤ c · L`, and the boundaries: the empty input,
   `s = 0`, `M.k = 0`, empty fields.
2. **The route refinements (the review's F2; accepted by the user, 2026-10-24).** (a) The clock
   writer's rounds run as phases of one phase host (`Turing.phaseHostTM`), not a `seamCompTM`
   round machine; (b) the exits are a stationary leaf phase written in this file, where the brief
   allowed only "a one-step exit dispatch… Nothing else"; (c) the certification uses F2's own
   last clause instead of `Turing.windowRun_stop_unique`. Is each sound, and within the brief's
   ground rules (no new public name, no admission, no unpublished lemma)?
3. **Rule 10** (with the scope of 2026-10-23: it binds TCSlib's own definitions; core and
   Mathlib definitions may reduce in `rfl`/`decide`/`show` but are never passed to
   `simp`/`rw`/`unfold`). The review's seal: 34 definitions (the worker's 32 and the two derived
   `Fintype` instances), the body 0 errors under it, all 34 `rfl` controls close unsealed and fail
   sealed; every `rw`/`simp`/`unfold` argument classified by name resolution (review §(c), out/).
   Does any step still close only because another file's definition reduces? **Rule 11:** no R3
   row, no other file's private.
4. **Duplication.** The review's screen (the brief's 21-file population, under the lock): 1,058 →
   1,102 declarations, 513 → 521 pairs, 8 new, all inside `WindowClock`, the highest 88%
   (`cw_seg_back`/`cw_seg_skipS`, F3); none cross-file. Are the in-file pairs justified? Is any new
   private a re-derivation of a published lemma (`Turing.wordPatch_append`,
   `MultiTapeTM.spaceUsed_le_of_abs_le`, the phase-host lemmas, `Turing.inputRewindTM`)?
5. **The text.** A1 and A2, and the new docstrings and sketches: accurate, and public-facing (no
   campaign labels, paths or dates in Lean text)? The commit subjects keep the worker's
   "(F3 cont2, checkpoint N)" labels by the user's ruling.
6. **Records.** The review's F4 (the worker's seal dropped the two instances: an artifact of its
   control method) and F5 (no checkpoint zips in the inbox; three double blank lines; the status
   paragraph names private lemmas, as the base's did): any correctness gap?

## Repository-side attestations (verify or challenge)

- **Elaboration:** the review: the delivered file with no diagnostic at all, at the base
  (`oleans-lslsk`) and on both of #156's trees; each checkpoint with only the target's sorry. The
  maintainer: the landing head's file, against `oleans-lphl2` (the campaign's tree after #156),
  with no diagnostic (`campaign/fills/b6/evidence/b6-configclock-cont2-landing/`).
- **Axioms** (the review): the target and all 70 declarations of the file on
  `[propext, Classical.choice, Quot.sound]`.
- **Probes** (the review): the brief's import probe (102 checks), the consumer probe, the
  worker's 145-check probe and the join probe, standalone and appended to the module.
- **Sweep** (the worker; checked by the review): 182 modules, 28 → 27 sorry warnings, exactly the
  base set less the target.
- **Lint** (the landing head): `SpaceComplexity` 0 FAIL, 82 WARN over 107 files (81 at the base;
  the new one is the file's size, 1,679 lines); no added line over 100 characters.
- **Replay:** `replay-lf3c2.sh`, `WindowClock`'s downstream closure (2 modules: `WindowClock`, the
  `SpaceComplexity` facade) at `1911b1ca`, chained from `oleans-lphl2`. **Pending:** as for gates
  64–69, this gate is dispatched before the replay; the PR is clear to merge only when both have
  passed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/70-b6-configclock-cont2-fill/findings.md`. The gate closes when it has zero
blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named `b6-configclock-cont2-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
