# fills-8: B5a canonizer and H1 continuation 2, record tables continuation 4: integration record

Side branch `integrate/fills-8` (PR #84), on the campaign tip `385d6e5a`. Each delivery was applied by
`git am -3` with Codex authorship. All three agents worked from `6aa9f67b`, which descends from the
briefs' required ancestor `235de343`. Neither owned file changed between that base and the
integration base. The two B5a batches own disjoint declarations of `CodeSimulator.lean`: the
integrated file is exactly the conflict-free 3-way merge of the two deliveries over the base
(6,226 lines). The record tables are byte-identical to their delivered snapshot.

| Delivery | Brief | Agent commit (base) | Integrated | Report |
|---|---|---|---|---|
| B5a, the canonizer, continuation 2 (partial) | `briefs/b5a-fill-canon-cont2.md` | `84c0abe7` (`6aa9f67b`) | `75c7f5a3` | `audits/b5a-fill-agent-reports/canon-3-REPORT.md` |
| B5a, H1, continuation 2 (partial) | `briefs/b5a-fill-h1-cont2.md` | `8382896a` (`6aa9f67b`) | `ad6db27f` | `audits/b5a-fill-agent-reports/h1-3-REPORT.md` |
| §12.8b record tables, continuation 4 (row 17 proved) | `briefs/w1-fill-recordtable-cont4.md` | `7158dd2b` (`6aa9f67b`) | `b2ab49aa` | `audits/wave1-fill-agent-reports/recordtable-5-REPORT.md` |

## Results

One public row closes, and no new admission is introduced: every new private is proved.
- **Record tables: 1/2.** Row 17, `exists_recordTemplateTM`, is proved, with standard axioms only,
  by 28 privates. The bound phase runs the inherited digit-bound writer on a clean lifted bank; the
  window phase builds the radius window on an isolated digit bank with the public `expandTM` and
  counter loop, then copies it into the destination. The table is at **15 of 20** rows. Row 18,
  `exists_recordInitTM`, keeps its admission; the report's frontier builds it from row 17.
- **B5a canonizer: 0/1.** 14 privates. The total two-port parse front end
  `exists_canonParseFront`: header validity joined to the guard, a reject port with the exact
  fallback law and a ready-for-grammar port, in `a·(|input| + 1)` steps, silent. Promotion
  candidates disclosed: `exists_canonBoolBranch`, `canonSeam_avoids`, `canonExitDispatch`. The
  frontier: restore the binary bound after the destructive guard, the generic action-record
  validator, the grammar loop, the emission, note 50.
- **B5a H1: 0/1.** 11 privates. The binary deadline clock around the frozen step block
  (`h1Clock_effect`), hosted on the virtual input (`h1HostedClock_effect`), and its one-bit verdict
  (`h1HostedVerdict_accepts`), within `t·(50·(|table| + 1)) + 4t + 2|bits t| + 3` steps. It
  cites `h1Round_effect`, `counterLoopTM_run_done`/`_escape` and `vhostEmitTM_runFrom` rather than
  re-deriving them. The frontier: the nested-input startup, canonizer installation, the joint
  ledger, note 50.

## Verification (maintainer)

- **Integrity.** Every `SHA256SUMS` entry is OK (44, 49 and the record tables' set), and every file of
  each archive is listed. Each git bundle verifies inside the repository, needs exactly the base
  `6aa9f67b`, has its tip equal to the reported delivery commit, and changes only the owned file.
  Excluded, never compiled or run, and referenced by no patch: the environment shims
  (`readlink_compat.c`, `self-exe-compat.c`) and wrappers, and every agent script (freeze, screen,
  sweep, ownership and duplication checkers). Every added line of the three patches was scanned for
  `#eval`, `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`, `native_decide` and new syntax or
  elaborators: none.
- **Freeze** (`audits/logs/fills-8-freeze.log`; `declfreeze.py` v2 and the statement comparison
  `privstmt.py`):
  - no statement changed (public or private), no public was added or removed, no import changed;
  - privates added: canonizer 14, H1 11, record tables 28; none removed;
  - the changed publics are the four targets. `exists_polyCanonizer`, `exists_uniformSimulator`
    and `exists_recordInitTM` change only by a flagged docstring appendix: their comment-stripped
    code is identical and still ends in `sorry`. `exists_recordTemplateTM` keeps its statement and
    gains its proof;
  - the changed inherited privates are exactly the reports' scoped style edits:
    - the canonizer's one line wrap in `exists_canonGuardFront`;
    - H1's proof-body lint cleanup of its own 24 earlier declarations, statements unchanged;
    - the record tables' four whitespace-only wraps, checked token for token.
- **Elaboration** (`audits/logs/fills-8-elaboration.log`, read-only against the tip snapshot
  `oleans-r8`): 0 errors in both files.
  - `CodeSimulator` (both B5a deliveries): 2 sorry warnings (the two B5a rows), and one other
    warning: the unused binder `hr` in the frozen statement of `h1Seek_stateStep`, which the H1
    report escalates rather than edit. H1's 67 inherited linter warnings are down to that one.
  - `RecordTable`: 5 sorry warnings (rows 15, 16, 18, 19, 20).
- **Style.** No new line over 100 characters. Over-long lines: `CodeSimulator` 84 → 15 (H1's 14 are
  in frozen signatures and definition bodies, escalated by its report), `RecordTable` 34 → 28.
- **Duplication.** Each per-batch screen was run on its brief's population at the base, with only
  that agent's file replaced. **Each matches the agent's own screen byte for byte, before and
  after**, and the base screens equal the briefs' committed baselines.

  | Delivery | Before | After | Pairs |
  |---|---|---|---|
  | B5a canonizer | 2,020 / 2,221 | 2,033 / 2,223 | two new in-file, as disclosed: `exists_canonReadySeam` and `exists_canonHeaderCountSeam` against the new `canonBlankLift` (68%) |
  | B5a H1 | 2,020 / 2,221 | 2,030 / 2,220 | none new; `h1ReadActions_at` → `h1Table_groups` (55%) disappears with the cleanup |
  | Record tables | 1,952 / 2,249 | 1,979 / 2,250 | one new in-file, as disclosed: `rt_richWindow_run` against `rt_moveWord_run` (56%) |

  At the integration head, the B5a population gives 2,043 / 2,222: exactly the canonizer's two
  pairs are new and the H1 pair is gone (`audits/logs/fills-8-screen-b5a-pairdiff.txt`).
  **The combined screen at the integration head** (`audits/logs/fills-8-screen-combined.txt`, 36 files: the union of the two briefs' populations, `audits/evidence/fills-8/combined-screen-population.txt`; the same population at the base, `fills-8-screen-combined-base.txt`): 2,082 / 2,312 → 2,132 / 2,314. Exactly the three disclosed in-file pairs are new, the one H1 pair is gone, and **no cross-batch pair** appears (`audits/logs/fills-8-screen-combined-pairdiff.txt`).
- **Replay** (user-run; `audits/logs/fills-8-replay.log`, at `b2ab49aa`):
  `scripts/lean_check_tree.sh` over the downstream closure of the two changed modules, with fresh
  `.oleans` into `oleans-f8`, a copy of the tip snapshot. **15 modules, 0 errors.** The sorry
  warnings are exactly the open rows: RecordTable 5, CodeSimulator 2, ConfigGraph 1, and the
  unfilled chapter-4 files as before.
- **Axioms** (`audits/logs/fills-8-axioms.log`; probe `audits/evidence/fills-8/AxF8.lean.txt`,
  against the replay snapshot): every public of RecordTable, CodeSimulator, Codes2Tape, EXPCOM,
  Relativization and ConfigGraph, 80 in all.
  - No axiom outside `[propext, Classical.choice, Quot.sound]`, apart from the open rows'
    `sorryAx`.
  - 60 admission walks are empty. The other 20 rest exactly on the open rows: record-table rows
    15, 16, 18, 19 and 20, the two B5a rows (under which the `EXPCOM` cluster and
    Baker–Gill–Solovay sit), and `NSPACE_subset_exp_dtime`.
  - The private censuses find no `sorryAx`: RecordTable 470 constants, CodeSimulator 867,
    Codes2Tape 24, EXPCOM 39, Relativization 140, ConfigGraph 56.
  - Of the 80 walks shared with the fills-7 probe, the only change is `exists_recordTemplateTM`'s,
    now empty.

## Maintainer commits (comment-only)

- `739c99b3`: `CodeSimulator`'s module header status now describes fills-8 (the parse front end, the
  hosted clock and verdict) and the remaining open items.

## Disposition

- **H2 promotion window.** Both B5a continuations are integrated, so the H2-S round-1 ruling on O2
  applies: H2-M lands in a coordinated window before the next B5a continuation is briefed, with the
  move comparison recomputed against this integration base. H1's style cleanup changed the proof
  bodies of 24 step-block declarations (no statement), so the round-1 move probe is stale.
- **Escalations to decide.** H1's frozen-signature width lines (14) and the unused binder `hr`
  can be fixed only by editing frozen statement text (whitespace and a binder name); the H2-M move
  is the natural place, since it re-homes those declarations anyway.
- **Next briefs:** continuations for the three batches (row 18; the canonizer's grammar; H1's
  startup and ledger), after the H2 window.
