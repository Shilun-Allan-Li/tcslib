# fills-7: three continuation partials: integration record

Side branch `integrate/fills-7`, on the campaign tip `650d1aad` (after PR #72). Each delivery was
applied by `git am -3` with Codex authorship. Every owned file was unchanged between the agent's
base `9e34c048` (PR #67's merge) and the integration base, and the record-table file matches its
delivered snapshot byte for byte. The two B5a batches own disjoint declarations of
`CodeSimulator.lean`: H1 applied cleanly on top of the canonizer, and the merged file is the base
plus both insertions (4,942 lines, 188 privates: 78 inherited, 12 and 98 new), with no name in
common. The one maintainer commit is comment-only.

| Delivery | Brief | Agent commit (base) | Integrated | Report |
|---|---|---|---|---|
| §12.8b record tables, continuation 3 (partial) | `briefs/w1-fill-recordtable-cont3.md` | `bd520060` (`9e34c048`) | `9c85477a` | `audits/wave1-fill-agent-reports/recordtable-4-REPORT.md` |
| B5a, the canonizer, continuation (partial) | `briefs/b5a-fill-canon-cont.md` | `a9d7f1fd` (`9e34c048`) | `0cd53565` | `audits/b5a-fill-agent-reports/canon-2-REPORT.md` |
| B5a, H1, continuation (partial; **complete step block**) | `briefs/b5a-fill-h1-cont.md` | `df8aea13` (`9e34c048`) | `c3f82f8d` | `audits/b5a-fill-agent-reports/h1-2-REPORT.md` |

## Results

No public row closes, and no new admission is introduced: every new private is proved.
- **Record tables: 0/2** (rows 17–18). Continuation 3 proves row 17's bound-field prefix: the
  fixed-width increment, the one-cell overflow extension, the canonical binary output, and the
  transport onto an isolated rich-alphabet digit bank, in 21 privates. The table stays at 14 of 20
  rows. The report's frontier: connect the bound writer to the destination field, build the
  window with two radius counters, map and clean up, package row 17, then row 18.
- **B5a canonizer: 0/1.** 12 privates. The guard front end prepares the header, its successor
  count and the native remainder address from blank tapes, seeks there, runs the inherited guard,
  and seeks back on success, in linear time. The frontier: the header-validity branch, a
  generic action-record validator (a promotion candidate, not yet built), the grammar loop, the
  emission, and the note-50 executions.
- **B5a H1: 0/1, with the complete generic step block.** 98 privates. `h1RoundTM k` is one finite
  machine per work-tape count `k`, whose control does not depend on the coded state count. It
  performs record lookup in the serializer's read order, the selected record's payload,
  successor installation and the round seam. `h1Round_effect` gives `0 < T ≤ 50·(|table| + 1)`,
  a strict interior, unchanged output at every prefix, and a head envelope. This is host H2 of
  design §14, proposed for promotion (below). The frontier: startup and canonizer
  installation, the Z1-hosted binary clock, the verdict and joint ledger, then note 50.

## Verification (maintainer)

- **Integrity.** Every `SHA256SUMS` entry is OK: 35, 50 and 102. Each git bundle verifies inside
  the repository, needs exactly the base `9e34c048`, has its tip equal to the reported delivery
  commit, and changes only the owned file. Excluded, never compiled or run, and referenced by
  no patch:
  - the environment shims `self-exe-compat.c` (twice) and `readlink_compat.c`;
  - the agent scripts `freeze_check.py` (twice), `screen_check.py`, `sweep_check.py`,
    `admission_census.py`, `run_final_probes.py`, `run_sweep.py`, `env.sh`, `lean-wrapper.sh`,
    `environment.sh`, `package-delivery.py`, `screen-new.py`, `verify-freeze.py`,
    `verify-sweep.py`, and H1's copy of `copy-text-screen.py`.

  Every added line of the three patches was scanned for `#eval`, `run_cmd`, `IO`, `unsafe`,
  `implemented_by`, `extern`, `native_decide` and new syntax or elaborators: none.
- **Freeze** (`audits/logs/fills-7-freeze.log`; maintainer tool `declfreeze.py` v2, which now
  ignores lines inside comments):
  - no statement changed, and no public was added or removed;
  - privates added: RecordTable 21, CodeSimulator 12 and 98, with none removed or changed;
  - the only changed public declarations are the targets (`exists_recordTemplateTM`,
    `exists_recordInitTM`, `exists_polyCanonizer`, `exists_uniformSimulator`). Each change is a
    flagged docstring appendix: the code after each docstring is byte-identical;
  - no import changed;
  - each other diff hunk is a pure insertion. H1's diff shows the target's docstring as removed
    and re-added, an alignment artifact; the declaration-level check finds no line removed.
- **Elaboration** (`audits/logs/fills-7-elaboration.log`, read-only against the fills-6/CH34-D4
  snapshot): 0 errors in both files.
  - `RecordTable`: 6 sorry warnings, the six open rows (15–20).
  - `CodeSimulator`: 2 sorry warnings (the two B5a rows), plus **67 linter warnings, all in H1's
    new block**: 41 unused `simp` arguments, 8 unreachable tactics, 7 `<;>` suggestions, 6
    `omega` that do nothing, 2 `simpa` → `simp`, 2 no-op `congr 1`, and 1 unused variable.
- **Style.** Lines over 100 characters added: H1 83, record tables 8, canonizer 1
  (`scripts/style_lint.py` does not check width). With the linter warnings, these go to each
  owner's next continuation (backlog F7-1(e)).
- **Duplication.** Each per-batch screen was run on its brief's population at the base, with
  only that agent's file replaced. **Each matches the agent's own screen byte for byte, before
  and after.**

  | Delivery | Before | After | New pairs |
  |---|---|---|---|
  | Record tables | 1,851 / 2,237 | 1,867 / 2,237 | none |
  | B5a canonizer | 1,920 / 2,209 | 1,931 / 2,212 | three in-file, as disclosed: `exists_canonOffsetTM` against `exists_canonCountTM` (68%), and `canonStrictInstall` against `exists_canonHeaderSeam` both ways (57–59%) |
  | B5a H1 | 1,920 / 2,209 | 1,994 / 2,218 | nine in-file, as disclosed and justified pair by pair in the report (50–71%) |

  **The combined screen at the integration head** (`audits/logs/fills-7-screen-combined.txt`,
  36 files: the union of the two populations; the same population at the base,
  `fills-7-screen-combined-base.txt`): 1,981 / 2,300 → 2,082 / 2,312. Exactly the twelve
  disclosed in-file pairs are new, and no pair disappears. **No cross-batch pair:** the
  pre-disclosed fixed-field record-walk overlap between the two B5a batches does not appear in the
  text screen. It stays for the maintainer to factor (F7-1(c)).
- **Semantic overlap the screen does not see.** The canonizer's `canonEmbedEq` is the R1
  configuration-reconstruction argument: from the selected-bank projections and the unchanged
  ambient frame, conclude equality of an embedded configuration. That is the family of the
  wave-1 gate's major F1 (`oracleBankCfg_eq` against `Loop.emCall_exit_fixed`). The report
  discloses it as a promotion candidate and names the `Primitives`, `CertShell` and `OracleSim`
  analogues. Recorded as a member of that family (F7-1(b)).
- **Replay** (user-run; `audits/logs/fills-7-replay.log`, at `91c3594a`):
  `scripts/lean_check_tree.sh` over the downstream closure of the two changed modules, with fresh
  `.oleans` into a copy of the snapshot. **15 modules, 0 errors.** The sorry warnings are exactly
  the open rows: RecordTable 6, CodeSimulator 2, ConfigGraph 1, and the unfilled chapter-4 files
  as before.
- **Axioms** (`audits/logs/fills-7-axioms.log`; probe `audits/evidence/fills-7/AxF7.lean.txt`,
  against the replay snapshot): every public of RecordTable, CodeSimulator, Codes2Tape, EXPCOM,
  Relativization and ConfigGraph, 80 in all.
  - No axiom outside `[propext, Classical.choice, Quot.sound]`, apart from the open rows'
    `sorryAx`.
  - 59 admission walks are empty. The other 21 rest exactly on the open rows: the six
    record-table rows, the two B5a rows (under which the `EXPCOM` cluster and
    Baker–Gill–Solovay sit), and `NSPACE_subset_exp_dtime` (S1b's two corollaries).
  - The private censuses find no `sorryAx`: RecordTable 342 constants, CodeSimulator 786,
    Codes2Tape 24, EXPCOM 39, Relativization 140, ConfigGraph 56.
  - All 71 walks shared with the fills-6 probe are unchanged.

## Maintainer commits (comment-only)

- `8aa899c0`: `CodeSimulator`'s module header now gives the fills-7 status, since it still listed
  the step block's lookup, installation and round seam as open.

## Disposition

- **H2 promotion** (design §14, host-first rule): the complete step block is promoted by PR and
  gate before any second consumer is briefed. Its named consumers are B6's `U₀` (RD-3), C1,
  U-1 and EXPCOM. H1's own assembly continues on the private copy (F7-1(a)).
- **Next briefs:** continuations for the three batches, each also clearing its own style debt.
  The replay has passed, so they can be issued.
