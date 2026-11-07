# MIG-1 megafill — checkpoint cp07 (F-D deletions and consumers) — PARTIAL

Agent: Claude (Anthropic). Branch `fill/mig1-mega` from exactly
`83ac315ed9e7089466bd16a32f3b71fbadc556d2`; records `7df0d047d501a1d08982d17d20208faf49d39131`.
Commits: `COMMITS.txt` (F-A ×2, F-C, F-B, F-D). Verdict: **partial (checkpoint)**.

## F-D results
- Catalog imports `TCSlib.Complexity.TuringMachine.Build.Primitives` (approved; acyclic — the
  641-module order lists Primitives before Catalog, `final-order-check.log`).
- The twenty space rows are short corollaries of named specs (adapted from gate 16's Catalog
  part): `computesFunInTime_{id,const,prepend,lengthBits,polyUnary,polyBits,pairEncodeFixed,
  pairFst,pairSnd,pairValid,pairConcat,pairDup,pairLenCheck,stripLast,incFixed,pairMapSnd,
  splitSolve}_spaceUsed`, `redirectTM_spaceUsedByTape` (now via `spaceUsedByTape_eq_card` and
  `mem_visitedByTapeHead_iff` instead of unfolding), `computesFunInTime_cond_spaceUsed`,
  `exists_loopTM_spaceUsed`. Statements unchanged.
- Pruning by reachability from public declarations (`tools/prune.py`, `fd-prune-1.log`): all 356
  `f2_` / `a2_` / `catalog_redirect*` private declarations (8,202 lines) are unreachable and deleted;
  36 private declarations remain (the catalog sweep/compare/increment/seek/scan machinery, none a
  copy). Each moved argument has exactly one home: Simulation (`branchTM_spaceUsed`), Wrappers
  (conditional ledger), TimeConstructible (counter space), Loop (extended contract, seam space),
  Primitives (poly space, forwarding map). Fates follow the gate's semantic table, not a slice;
  the only "move" fate not realised as a separate lemma is `f2_first_length`, which
  Primitives' existing `pairLenCheckTM_computes` proof did not need.
- **Six public removals** (`Turing.transferTM_run`, `copyTM_run`, `clearTM_run`, `compareTM_run`,
  `incrementTM_run_succ`, `incrementTM_run_overflow`). Consumers re-pointed: CertShell's loader
  (one copy, three transfers) and CodeSimulator's copy now read `copyTM_run_ofCfg` /
  `transferTM_run_ofCfg` at canonical seams with `Cfg.ofWords_copy_endpoint` /
  `Cfg.ofWords_transfer_endpoint` and `Cfg.ofWords_workTapes`/`_workTapePos`; prose pointers in
  Catalog and CertShell updated. Final-tree candidate enumeration:
  `retirement-consumers-final-lean.txt` (**0** hits in `TCSlib/`);
  `retirement-consumers-final-nonlean.txt` (8,113 hits, all in records except three live documents
  outside the owned files — `machine-library-design.md` (2), `campaign/backlog.md` (1),
  `campaign/design/plans/AroraBarakChapters3-4Plan.md` (1) — reported for the maintainer).
- WordSize: documentation-only (one line: `Build/Catalog.lean:4318` → `:1980`, the current line
  of `computesFunInTime_lengthBits_spaceUsed`); declarations untouched.

## Checks (fresh)
`elab/fd1.summary` (Catalog exit 0, 0 errors, 0 sorry, 33 warnings), `tail-fd1/summary.log`
(34 bootstrap modules downstream of Catalog including CertShell and CodeSimulator: failed=0),
`elab/fd2.summary` (CertShell after its prose edit; WordSize); `freeze-cp07.log` — **PASS**:
public added exactly the 3 forwarding exports, removed exactly the 6 retired rows, no header,
visibility, order or definition-body change, imports changed only by the two approved additions;
`changed-files.txt` (only the 11 owned files differ from the base); `static-sorry-cp07.log`
(TOTAL 3: the frozen RAM admissions).

## In progress / NOT RUN at cp07
The 641-module final sweep (`final-sweep-1/`, started at the F-D commit, running at packaging
time — its partial log is included), both fresh screens (running), axiom walks for the F-D
rows, the compiled census, F-D seals, the Primitives seal repairs, policy lint.
