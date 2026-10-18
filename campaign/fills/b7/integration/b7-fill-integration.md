# B7 fill, first delivery (partial, targets 1–6): integration record

Brief: `briefs/ch34-b7.md` (ancestor `315571be`). Delivery: `infra_local/fill-ch34-b7.zip`,
agent commit `b5484946` on base `a1999089`. The agent's report is
`audits/b7-fill-agent-reports/fill-1-REPORT.md`.

## Result

**6 of 12 proved**, a partial delivery under the brief's continuation provision (ground
rule 9). There is no escalation and no mathematical obstruction: the agent stopped at its
budget.

| # | Target | Status |
|---|---|---|
| 1 | `LogProg.OIS.run` | proved |
| 2 | `LogProg.OIS.compile_decides` | proved |
| 3 | `mem_LOGSPACE_preimage` (N2) | proved |
| 4 | `mem_LOGSPACE_of_logspaceReducible` (T3) | proved |
| 5 | `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` (T5) | proved |
| 6 | `LogProg.readIn_run` | proved |
| 7–12 | N1, N3, N4, `comp`, `trans`, `multLang_mem_LOGSPACE` | original sorries kept; continuation brief `briefs/ch34-b7-cont.md` |

There are no admitted helpers and no target proved modulo an admission. The six proved
targets depend on nothing unfilled.

## Verification (maintainer)

- **Integrity.** All 26 `SHA256SUMS` entries are OK. The zip's C file
  (`evidence/lean-self-path.c`, an `LD_PRELOAD` shim for the agent's own environment) is
  excluded: it was never compiled or run, and neither the patch nor any source references it.
  The agent's helper scripts (`final-sweep.sh`, `freeze-check.py`) were not run either.
- **Integration.** `git am -3` applied the one-patch series cleanly at the campaign tip
  `9b47f7b9`, keeping the agent's authorship. The owned files are unchanged between the
  agent's base and the tip. All five owned files then match the delivered snapshots byte for
  byte.
- **Freeze** (`audits/logs/b7-fill-1-freeze.log`, the maintainer's own check).
  - No statement changed, and no public was added or removed.
  - Bodies changed only at the six targets.
  - 30 private helpers were added (14 in `InputAccess`, 16 in `PreimageHost`), matching the
    report's lists. No other declaration's text changed.
  - Outside declarations, only the flagged status text changed ("sorried" or "spec, fill
    pending" to "proved").
  - Imports are unchanged.
  - No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in
    the added lines.
- **Duplication** (`audits/logs/b7-fill-1-screen-after.txt`). The maintainer's re-run is
  byte-identical to the agent's: 192 → 227 declarations, 53 → 58 pairs. All 5 new pairs are
  in-file `InputAccess` pairs at 53–62%, each justified in the report; there is no
  cross-file pair and none disappeared. **New copies: none.** No ledger change.
- **Lint** (`audits/logs/b7-fill-1-stylelint.log`): 0 FAIL, 0 WARN.
- **Sizes**: `InputAccess` 541 lines, `PreimageHost` 822, `Reductions` 153.
- **Replay** (`audits/logs/b7-fill-1-replay.log`). 8 modules, the downstream closure of the
  three changed files, at `b0738c89` into a snapshot of the B7 statement olean tree; the user
  ran it from the maintainer's command. **0 errors.** 11 sorry warnings: `InputAccess` 1,
  `QueryReshape` 2, `Reductions` 2, `Path` 2, `ImmermanSzelepcsenyi` 3, `Mult` 1. That is
  the statement sweep's 17 minus the six filled targets.
- **Axioms** (`audits/logs/b7-fill-1-axioms.log`). The pre-ship probe, read-only against
  the replay's olean tree, gives 0 errors.
  - The six filled targets print `[propext, Classical.choice, Quot.sound]`.
  - Targets 7–12 and the four declarations that depend on them (`inputBitLang_mem`,
    `inputLenLang_mem`, `comp`, `trans`) still print `sorryAx`, as expected.
  - The proved helpers' prints are unchanged.

## Disposition

- This partial goes in by PR. The **B7 fill gate** runs once the continuation completes all
  twelve targets, and covers both deliveries. This follows the ZF partials' precedent.
- The continuation brief issues at the merged commit, so that its agent starts from targets
  1–6 proved.
