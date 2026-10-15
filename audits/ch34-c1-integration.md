# Epoch C1 and S1a — integration record (2026-10-10)

Five chapter fill batches were delivered complete and integrated by `git am -3`
with Codex authorship, on top of the merged G1 (PR #15, `df2da2ed`):

| Batch | Brief | Targets | Exports (sanctioned) | Commits |
|---|---|---|---|---|
| C1a | `briefs/ch34-c1-batchA.md` | 9/9 | none | `1a3fe32d` |
| C1b | `briefs/ch34-c1-batchB.md` | 13/13 | `evenScanTM`, `evenScanTM_decidesInTime` | `75cfe2e6` |
| C1c | `briefs/ch34-c1-batchC.md` | 10/10 | E1–E5 in `OracleNondeterministic` | `8855d526` |
| C1d | `briefs/ch34-c1-batchD.md` | 6/6 | none | `43268b2e`, `3555b51c` |
| S1a | `briefs/ch34-s1-batchA.md` | 4/4 | E1–E4 in `ConfigGraph` | `85e17ca4` |

**42 statements filled.** No escalations, and the proved-modulo set is empty.
C1d's PSPACE collapse cited C1a's `P_subset_PSPACE` under the citation rule. With both
landed, it prints no `sorryAx`.

## Maintainer verification

- **Integrity:** every `SHA256SUMS` is OK, and no patch references a C file
  (the zips' runtime shims are excluded and unused). None of the agents'
  scripts was run. All 17 integrated files are byte-identical to the
  delivered sources, and the diff from `df2da2ed` touches exactly those 17
  files.
- **Freeze** (`audits/logs/c1-integration-freeze.log`), a declaration-level
  check per owned file:
  - no statement changed, and no public declaration was removed;
  - the changed bodies are exactly the targets;
  - the added publics are exactly the sanctioned exports (C1b 2, C1c 5,
    S1a 4).
- **Replay** (`audits/logs/c1-integration-replay.log`): the downstream
  closure of every changed module (G1's four files, `CounterLoop`'s doc
  refresh, and the 17 fill files), 196 modules in dependency order with
  fresh `.olean`s and `ComputationalModels` excluded: **0 errors**. The
  remaining sorries in the owned files are exactly the out-of-scope
  statements: `Inclusions` 2, `Classes` 4, `TQBF` 4, `Logspace/Reductions` 4,
  `Relativization` 3, `ConfigGraph` 3 (the S1b summit).
- **Axioms** (`audits/logs/c1-integration-axioms.log`): 56 prints (all
  targets, the exports and the helpers the agents printed), all within the
  standard triple. No `sorryAx`.
- **Lint** (`audits/logs/c1-integration-stylelint.log`): 0 FAIL in
  `TuringMachine`, `SpaceComplexity`, `ClassOracle`, `ClassPSPACE`,
  `Formulas` and `Diagonalization`.
- **Duplication** (`audits/logs/c1-integration-screens/`: each brief's screen
  list, run before at `df2da2ed` and after):
  - **C1a:** no new pair.
  - **C1b:** one cross-file pair, the brief's pre-named expected pairing
    (`evenLang_mem_LOGSPACE` ↔ `evenLang_mem_SPACE_zero`, 82% and 60% of 131-
    and 179-character bodies: both are the shared scanner export plus the
    zero-tape bridge).
  - **C1c:** five new in-file pairs at 54–65%, all under the 90% copy line.
  - **C1d:** no new pair. None of its pre-named pairings occurred.
  - **S1a:** no new pair of its own. The one listed pair is C1c's, because
    `OracleNondeterministic` is in S1a's list.

  The epoch C1 fill gate rules on all of these.

## Next

The **epoch C1 fill gate** covers C1a–C1d, S1a, and the two maintainer
pre-issue promotions (`44853c6f`, `447a6cc3`). Its pack follows on this branch.
