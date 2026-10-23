C1, R continuation 2 (`TuringMachine/NDCodeSimulator.lean`): **the interpreter core
`Turing.exists_ndInterpreterCore` is proved**, modulo exactly the per-code replay canonizer
`Turing.exists_replayCanonizer` (still sorried). Delivered as item 1 of megafill A
(`fill-c1-core-cont2.zip`, SHA-256 `4a2896a3…ce9b`), complete.

**Commits** (on the campaign branch at `86523ba5`):
- 16 of the delivery's 19 commits (`6f6ca79b..ed9cb1ad`, on the base `6cfee544`), applied by
  `git am -3` restricted to the owned file, with the worker's authorship and subjects (the user's
  ruling): the delivery also commits its evidence logs to an `evidence/` tree, which stays out of
  the library (three evidence-only commits skipped, and one commit's `evidence/` part). The owned
  file comes out as the delivered blob `7d1657b3`;
- `5825c7b6`, the maintainer's (the review's F1, the user's ruling): six steps closed only by
  unfolding another file's definition (`MultiTapeTM.runFrom` in the rewind leaf's run, four;
  `CodeNDTM.toFinNDTM` in the verdict's `if`, two). They now read those through published
  equations; proof-only, the axioms unchanged;
- `f48ea176`, the maintainer's, docstrings only: the module's contents line and the facade's line
  ("the core is proved; the canonizer is sorried"), and an `Implementation.` paragraph naming the
  core's twelve phases.

**Review** (sub-agent; `campaign/fills/c1/reviews/core-cont2/REVIEW.md`; "complete; land with the
rule-10 fix"):

| Check | Result |
|---|---|
| Integrity | the zip and its 34 internal sums; the bundle's only prerequisite the base; the 19 patches reproduce every commit and the file |
| Scope and freeze | the owned regions only; the target's statement and docstring byte-identical; the overlay's 20 helpers verbatim, 5 new; 3 → 3 public declarations (at source) |
| Elaboration | 0 errors at the base and at the tip; only the canonizer's sorry warning |
| Axioms | the target's `sorryAx` only through `exists_replayCanonizer` |
| Rule 10 | no seal by the worker; the review sealed 46 definitions: six steps failed, fixed here (both seal variants and all 50 controls pass with the fix) |
| Probes | the brief's, and a 238-check extended probe, 0 errors |
| v3 screen | 460 → 465 declarations, 118 → 120 pairs; one 69% cross-file pair (three lemma names, an idiom pair; accepted, the user) |
| Lint | 0 FAIL; the one new WARN is the file's size |
| Sweep | the census 38 → 37, only the target's entry gone |

The maintainer re-elaborated the landed file against `oleans-lu2sc1` (only the canonizer's sorry
warning; the target on `[propext, sorryAx, Classical.choice, Quot.sound]`, `sorryAx` through the
canonizer only). The private `ic_rewind_scan` re-proves the public `FinTM.rewind_scan`; it is
ledgered (IR-1) and re-points when the input-rewind API lands (the user's ruling).

**Order.** After #149 (its closure contains this one's). This closure (`NDCodeSimulator`,
`Diagonalization/NTimeHierarchy`, `Diagonalization`, the facade) meets #147's at the facade
only, and megafill A's other two landings beyond it: whichever merges later replays.

**Replay:** after #149 merges. **Pending.**

**Gate:** a fill gate. **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)

