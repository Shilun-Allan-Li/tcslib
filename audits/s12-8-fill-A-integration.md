# §12.8 fill, stream A (Catalog Part 3 and the two-exit seam): integration record

Brief: `briefs/s128-fill-A.md` (ancestor `182e6f44`). Delivery: `infra_local/fill-s128-A.zip`,
agent commit `5aa646d6` on base `37ab6091`. The agent's report is
`audits/s12-8-fill-agent-reports/A-REPORT.md`.

The patch was applied at the campaign tip `c280727c`, which already contains streams B and C
(PR #41), as `3e856480`. Streams B and C are recorded in `audits/s12-8-fill-integration.md`.
Stream D is in PR #38, held for its R8.0b gate.

## Result

**Complete, 13/13.** There is no admitted helper, the proved-modulo set is empty, and there is
no escalation.

| # | Target | Route |
|---|---|---|
| 1 | `fieldsTape_field` | induction on the field index, through the public layout lemmas |
| 2–4, 6 | `scanResult_fold`, `_map`, `_shiftRight`, `_carry` | `scanResult_keep`, then one structural induction each |
| 5 | `scanResult_shiftLeft` | target 4 on the reversed word; no new induction |
| 7 | `scanTM_run_ofCfg` | **one** `catalog_trace_run` instance for both passes |
| 8 | `compareTM_run_ofCfg` | the existing compare trace, generalized in place; no second compare trace |
| 9–12 | `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg` | one shared pass lemma `catalog_pass_contract` (H-pass), with no time induction |
| 13 | `seamCompTM₂_run_ofCfg` (Seam) | both branches through `seamCompTM_runFrom_left` and `seamCompTM_run_ofCfg`; no new induction |

There are also the brief's two public body swaps:
- `compareTM_run` and `compareTM_spaceUsedByTape` now cite the generalized trace at
  `Cfg.ofWords`. Their statements are byte-identical.
- They keep the aliased `fst = snd` case.
- The frozen `hne` of `compareTM_run_ofCfg` is consumed explicitly (D2).

**With this delivery, `Catalog` is fully proved.** On this branch, so are stream C's three
rows that were proved modulo other streams (`exists_inputCallTM`, `exists_recordTestTM`,
`exists_recordEqTM`). The only open §12.8 row across streams A–C is `exists_recordStepTM`.

## Verification (maintainer)

- **Integrity.** All 41 `SHA256SUMS` entries are OK. The zip's C file
  (`evidence/lean-self-path.c`, an `LD_PRELOAD` shim for the agent's environment) is excluded:
  it was never compiled or run, and neither the patch nor any source references it. The zip
  contains no scripts.
- **Integration.** `git am -3` applied the one-patch series cleanly at `c280727c`, keeping the
  agent's authorship. `Catalog.lean` and `Seam.lean` are unchanged between the agent's base
  and the tip, and both match the delivered snapshots byte for byte.
- **Freeze** (`audits/logs/s12-8-fill-A-freeze.log`, the maintainer's own check).
  - No statement changed. No public was added or removed.
  - Bodies changed only at the 13 targets and the two authorized swaps.
  - 12 privates added in Catalog Part 3, matching the report's table; none in Seam.
  - The only existing privates changed are the four authorized in-place compare
    replacements: `catalog_compare_stop`, `catalogCompareF`, `catalogCompareR`,
    `catalog_compare_trace`. `catalog_compare_stop`'s body is byte-identical, since its types
    alone are generalized. No canonical compare trace survives beside the generalized one
    (hazard 1).
  - Outside declarations, only the flagged status labels changed ("statement layer" to
    "proved", and Seam's status paragraph).
  - Imports are unchanged.
  - No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in
    the added code. The one textual hit is docstring prose ("admit no adjacent blanks").
- **Duplication.** The maintainer ran the brief's two populations before (at the tip) and
  after (at `3e856480`). The tip already contains B and C, so these are the base of record,
  not the issue-time base `audits/logs/s12-8-fill-A-screen-base.txt`.

  | Population | Before | After |
  |---|---|---|
  | Primary (`audits/logs/s12-8-fill-A-screen-{before,after}.txt`) | 594 declarations, 423 pairs | 620 declarations, 430 pairs |
  | Extended, with `Sweep` and `StateRenaming` (`…-screen-ext-{before,after}.txt`) | 612 declarations, 429 pairs | 638 declarations, 436 pairs |

  Both populations give the report's delta exactly:
  - **8 new in-file pairs**, 50–69%, each justified in the report: the H-pass instances
    against each other, the two Mealy-induction instances, and the D4 compare/space pairs.
  - **4 changed pairs**, all compare/space pairs inside the acknowledged R3 sibling family;
    D4 keeps them unfactored. The highest is 74%.
  - **1 pair removed**: `compareTM_spaceUsedByTape` ← `clearTM_spaceUsedByTape`.
  - **No cross-file pair**, and nothing against `Sweep` or `StateRenaming`.
  - The agent's first screen caught two pairs at 90% or more. They were factored into the one
    shared `mealyRun_induction` before delivery.

  **New copies: none.** Catalog's acknowledged ledger members do not grow, so the D5 binding
  rule is met and no `backlog.md` item is triggered. No ledger change.
- **Lint** (`audits/logs/s12-8-fill-A-stylelint.log`): 0 FAIL. There are 15 WARN over
  `TuringMachine` and 7 over `TuringMachine/Build`, all size warnings. Catalog's predates this
  fill.
- **Sizes.**

  | File | Lines | Change |
  |---|---|---|
  | `Catalog` | 12,732 | from 11,970 |
  | `Seam` | 854 | from 815 |

  Catalog's split remains the acknowledged 12.2c work, and size alone is not a driver (user,
  2026-10-11).
- **Replay** (`audits/logs/s12-8-fill-A-replay.log`). 19 modules, the downstream closure of
  `Catalog` and `Seam` at the tip, at `3e856480`. The snapshot was a tip-consistent olean tree,
  with #39's fresh Logspace oleans overlaid for the `SpaceComplexity` facade. The user ran it
  from the maintainer's command.
  - **0 errors.** 10 sorry warnings, exactly the predicted set:
    - `CounterLoop` 1 (R8.6, which waits on #38);
    - `Inclusions` 1 (`b2b_host_contract`);
    - `CfgRecord` 1 (`exists_recordStepTM`);
    - `TQBF` 4;
    - `Zone` 2;
    - `Codes2Tape` 1.
  - `Catalog`, `Seam`, `Scan` and `InputCall` are at 0, and so are the other nine modules.
- **Axioms** (`audits/logs/s12-8-fill-A-axioms.log`; probe
  `audits/evidence/s12-8/S128FillAAxioms.lean.txt`). Read-only against the replay's tree, the
  probe prints every public of `Catalog` and `Seam`. **All 107 are within
  `[propext, Classical.choice, Quot.sound]`.**
- **Admission walk** (`audits/logs/s12-8-fill-A-admissions.log`). On this branch, these have
  no constant in their closure that mentions `sorryAx`:
  - `exists_recordTestTM`, `exists_recordEqTM`, `exists_inputCallTM`;
  - `scanTM_run_ofCfg`, `seamCompTM₂_run_ofCfg`.

  `exists_recordStepTM` rests only on itself.

## Disposition

- This PR can merge now.
- The **§12.8 fill gate** for streams A–C runs once C's step-row continuation completes. It
  covers this delivery and `audits/s12-8-fill-integration.md`. Stream D has its own R8.0b gate.
- The continuation brief for `exists_recordStepTM` can now issue against a tree where every
  row it may cite is proved. Its permitted modulo set (the nine stream-A rows) becomes empty in
  practice.
