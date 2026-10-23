# External audit pack — MIG-12 continuation 1: `Build/CfgRecord` onto the contract layer (PR #150, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, the machine library's migration onto framed
contracts (MIG, `machine-library-design.md` §16a). MIG-12 moves `Build/CfgRecord`, the §12.8
configuration-record rows, onto the contract layer (`Build/Contract`). It is a **swap**: every
public statement and docstring of the module is frozen. Only the proofs, and the private
bookkeeping under them, change. Phase 1's two commits came from the fill's earlier round (its
review: `campaign/fills/mig12/reviews/round1/`) and were supplied to **continuation 1**
(`campaign/fills/mig12/briefs/mig12-fill-cfgrecord-cont1.md`) as patches. Continuation 1's first
attempt stopped at an environment limit (`campaign/fills/mig12/reports/cont1-eres-REPORT.md`); its
rerun was delivered complete on 2026-10-22 (phases 1–4, `fill-mig12-cfgrecord-cont1.zip`, SHA-256
`0e29da88b32bd7deb0b6643d3cd6755fc16fee65be8106cc5907ff71c8fe23c6`). The worker's report is
`campaign/fills/mig12/reports/cfgrecord-cont1-REPORT.md`; the maintainer's review is
`campaign/fills/mig12/reviews/cfgrecord-cont1/REVIEW.md` ("complete; land with edits").

**The head:** `lean/mig12-cfgrecord-cont1` at `79de6551`, on the campaign branch at `e9b48616`.
This bundle's records are from a later records commit (stated in the bundle's README).
- `806143bc`, `e4f99da0`, `5ed67f8a`, `c3f6641f`, `2d8ba7ec`, `729e653e`: the delivery's six
  commits, cherry-picked from its verified bundle with their authorship kept (the user's ruling).
  The first two are round 1's (same patch-ids). They touch only the owned file. The result is the
  delivered blob `5b1feb62`;
- `79de6551`, the maintainer's (the user's rulings of 2026-10-22 on the review's F2–F4):
  - the module's status paragraph;
  - five stale passages in frozen public docstrings (F3: `RecordRun` twice in
    `exists_recordStepTM`, `recordRun_trans` in `exists_recordEqTM`, `compareTM_run_ofCfg` in
    `exists_recordEqTM`'s sketch, "Unfold `Turing.Cfg.init`" in `Cfg.inWindow_init`);
  - `recordStep_cell_write` re-proved through `Action.apply_workTapes` (F2: it closed only
    because `Action.apply` is `@[simp]`);
  - two private docstrings reworded and one "Proof sketch" added (F4).

## What changed (verify)

| Class | Declarations |
|---|---|
| **Public statements** | 21 → 21, every statement byte-identical; the public docstrings byte-identical to the base except the five F3 passages (`evidence/maintainer-commit.patch`) |
| **Public proofs changed** | the three rows `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM`, and `Cfg.inWindow_init` (`evidence/freeze-base-to-head.txt`; the tool counts a docstring edit as a body change) |
| **Privates** | 98 → 109. Removed: `RecordRun`, `recordRun_mono`, `recordRun_tagged`, `recordRun_trans`, `recordRun_zero` (the retired kit). Added: 16, including the contract readers `recordStep_contract_clauses(_range)` (the freeze lists them) |
| **Code after the delivery** | exactly the review's tested re-proof of `recordStep_cell_write` (`evidence/code-diff-delivered-to-head.txt`, `evidence/code-identity.txt`: the delivered file plus `probes/cell-write-fix.diff` equals the head, comments stripped) |
| **Size** | 5,302 lines at the base (5,310 after phase 1's patches) → 5,717 |

## Brief for the auditor

1. **The swap's fidelity.** Is every framed row (scan, skip, skip-back, copy, clear, compare,
   increment, decrement) now read through its contract (`Contract.segment` via `segment_iff`/
   `headBox_iff` and the row's field equations), with the one brief-authorized exception
   (`counterLoopTM_run_escape`, unchanged)? Are the 23 `_run_ofCfg` reads gone from the code, and
   the ledger's 73 explicit unfolding sites (`campaign/fills/mig12/inputs/mig12-fill-cfgrecord-cont1/unfold-sites.tsv`)?
2. **The freeze.** Every public statement byte-identical; the public docstrings identical except
   F3's five passages. Are those five edits exact descriptions of the new proofs and nothing more?
   Is any frozen docstring still describing a route the proof no longer takes?
3. **The route (the review's F1, accepted: the user ruled to close MIG-12 at its correctness and
   fidelity targets and to schedule a compression item).** The readers convert each segment back
   into the old run theorem's three scalar clauses, and about 67 lines turn the `Icc p p` envelope
   back into equalities. Is that conversion correct and complete, and does it re-introduce any
   unfolding or hand trace?
4. **Rule 10.** The review sealed 53 other-file definitions with 73 controls (fail sealed, pass
   unsealed). With `Action.apply` and `Cfg.init` also erased from the simp set, only
   `recordStep_cell_write` failed, which the maintainer's commit re-proves. Does any step still
   close only because another file's definition reduces or is `@[simp]`? Rule 11: no R3 row, and
   no other file's private (the review's axiom walk found none reached at the head).
5. **Duplication (the review's N1).** The v3 screen: 870 → 879 declarations, 435 → 440 pairs; 6
   new directed pairs, all in-file and under 90% (the top, 84%, is the two contract readers); no
   cross-file pair. The brief says a swap should remove pairs: is the increase justified?
6. **The text.** The status paragraph, the F3 passages and the F4 rewordings: accurate and
   public-facing (no campaign labels, paths or dates in new Lean text)?
7. **Records.** The review's F5 lists ten report details (the worker's seal not checkable from the
   delivery; two empty logs; counts). Is any of them a correctness gap rather than a records gap?

## Repository-side attestations (verify or challenge)

- **Elaboration** (the review): the delivered head has 0 errors and 0 warnings at the base
  (`oleans-lseam2`) and at the tip (`oleans-lsk2`). The maintainer re-elaborated the landed file
  against `oleans-lsk2`: no output (`evidence/elab-CfgRecord-head-lsk2.out`).
- **Axioms** (the review): all 130 declarations on axioms within
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`; no other file's private reached.
- **Probe** (the review): the brief's 227 checks, standalone at the base and at the tip and
  in-module, 0 errors.
- **Seal** (the review): above (item 4); `reviews/cfgrecord-cont1/out/19-*`.
- **Lint:** `TuringMachine/Build` 0 FAIL, 33 WARN over 39 files; `CfgRecord`'s size warning
  predates this PR (`evidence/lint-build.txt`).
- **The sweep** (the worker): 280 modules, 0 errors, 83 sorry warnings equal by name to the base's.
- **Public constants** (the review's N2): compiler auxiliaries only
  (`copyTM_contract.congr_simp`, `compareTM_contract.congr_simp`, one renumbered `_proof_1_74`).
- **Replay:** `CfgRecord`'s downstream closure (52 modules, `evidence/down-cfgrecord.txt`)
  overlaps #149's beyond the facade, so this PR merges after #149 and then replays its closure from
  #149's merged-tree snapshot (the user's ruling). **Pending:** by the user's ruling (2026-10-23)
  this gate is dispatched before the replay, which is recorded when it passes. The PR is clear to
  merge only when both have passed. The branch merges cleanly with #149's head (`git merge-tree`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/64-mig12-cfgrecord-cont1-fill/findings.md`. The gate closes when it has zero
blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named
`mig12-cfgrecord-cont1-fill-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
