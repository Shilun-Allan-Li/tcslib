MIG-12 continuation 1 (`Build/CfgRecord.lean`): **the record rows read the catalog and counter
rows through their contracts**. `RecordRun` and the module's 23 `_run_ofCfg` reads are retired
onto `Turing.Contract.segment` and `Turing.Segment.trans`; the 73 explicit unfolding sites of the
rule-10 ledger are gone. All 21 public statements and docstrings' statements are unchanged, and
the module has no `sorry`. Delivered complete (phases 1–4), `fill-mig12-cfgrecord-cont1.zip`
(SHA-256 `0e29da88…c8fe23c6`).

**Commits** (on the campaign branch at `e9b48616`):
- `806143bc`, `e4f99da0`, `5ed67f8a`, `c3f6641f`, `2d8ba7ec`, `729e653e`: the delivery's six
  commits (`5d02122a..8b0b0bf4`, on the base `96d60278`), cherry-picked from its verified bundle
  with their authorship kept (the user's ruling). The first two are round 1's commits (same
  patch-ids). They touch only the owned file, unchanged on the campaign branch since the base;
- `79de6551`, the maintainer's (the user's rulings of 2026-10-22 on the review's F2–F4): the
  module's status paragraph; five stale docstring passages (`RecordRun` twice, `recordRun_trans`,
  `compareTM_run_ofCfg`, "Unfold `Turing.Cfg.init`"); `recordStep_cell_write` re-proved through
  `Action.apply_workTapes` (it closed only because `Action.apply` is `@[simp]`); two private
  docstrings reworded and one "Proof sketch" added. The code is otherwise the delivered file's.

**Review** (sub-agent; `campaign/fills/mig12/reviews/cfgrecord-cont1/REVIEW.md`; "complete; land
with edits"):

| Check | Result |
|---|---|
| Integrity | `SHA256SUMS` 46/46; the bundle's only prerequisite the base; 6 linear commits; patches = bundle = delivered file (blob `5b1feb62`) |
| Scope and freeze | the owned file only; 21/21 public statements and docstrings byte-identical; imports unchanged; 98 → 109 privates (11 added, none removed) |
| Elaboration | no output at the base (`oleans-lseam2`) and at the tip (`oleans-lsk2`) |
| Axioms | all 130 declarations on the standard three, no `sorryAx`, no other file's private |
| Rule 10 | a 53-definition seal with 73 controls (fail sealed, pass unsealed); with `Action.apply` and `Cfg.init` also erased from the simp set, only `recordStep_cell_write` failed, fixed here |
| Probe | the brief's 227 checks, standalone at the base and at the tip and in-module |
| v3 screen | 870 → 879 declarations, 435 → 440 pairs; 6 new, all in-file, under 90%; no cross-file pair |
| Lint | 0 FAIL |
| Sweep | 280/280, the base's 83 sorry warnings by name |

The maintainer re-elaborated the landed file against `oleans-lsk2` (no output), checked that its
code is the delivered file's with exactly the review's tested re-proof, and re-linted
(`TuringMachine/Build` 0 FAIL, 33 WARN over 39 files; `CfgRecord`'s size warning predates this PR).

**Size.** The design expected the swap to shrink the module by 1.6k–2.1k lines; it grew by 402
(5,310 → 5,717 with the maintainer commit), because the new readers convert segments back to the
old endpoint shape. **The user ruled (2026-10-22): close MIG-12 at its correctness and fidelity
targets and schedule a compression item** (a generic contract-segment reader).

**Order.** `CfgRecord`'s downstream closure (52 modules) lies inside #149's (the space API):
**merge #149 first** (the user's ruling); this PR then merges the campaign branch in and replays
its closure from #149's merged-tree snapshot. #147 meets this closure only at the facade.

**Replay:** after #149 merges. **Pending.**

**Gate:** a fill gate (gate 64). **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)

