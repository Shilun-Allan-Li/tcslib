# B7 fill, continuation 1 (partial, target 7): integration record

Brief: `briefs/ch34-b7-cont.md` (ancestor `fdce1a55`). Delivery:
`infra_local/fill-ch34-b7-cont.zip`, agent commit `689f6770` on base `37ab6091`. The agent's
report is `audits/b7-fill-agent-reports/fill-2-REPORT.md`. The first delivery's record is
`audits/b7-fill-integration.md`.

## Result

**Target 7 proved; the running total is 7 of 12.** This is a partial delivery under the
continuation provision (ground rule 9). There is no escalation and no mathematical
obstruction: the agent stopped at its budget while preparing target 8.

| # | Target | Status |
|---|---|---|
| 1–6 | first delivery | proved; frozen and unchanged |
| 7 | `implicitlyLogspaceComputable_id` (N1) | **proved**, standard axioms |
| 8 | `implicitlyLogspaceComputable_dropIdx` (N3) | original `sorry` kept; six private support lemmas proved |
| 9 | `ImplicitlyLogspaceComputable.compQ` (N4) | original `sorry` kept |
| 10 | `ImplicitlyLogspaceComputable.comp` | original `sorry` kept |
| 11 | `LogspaceReducible.trans` | original `sorry` kept |
| 12 | `multLang_mem_LOGSPACE` | original `sorry` kept |

There are no admitted helpers. Target 7 depends on nothing unfilled. With it, the first
delivery's dependants `inputBitLang_mem` and `inputLenLang_mem` are now admission-free too.

**Target 7's construction.**
- One call-free program with a mode bit serves both query languages.
- Four registers, with every physical read through the frozen `readIn_run`.
- Register updates come from the received increment, clear and rewind fragments.
- The space bound is `4 * (W + 2)` cells for `W = |bits (|y| + 1)|`, closed by
  `log_poly_bound`.

## New shared exports (flagged under the brief's rule 3)

There are three new public theorems in `InputAccess`, each with a `## Main results` bullet:

| Export | Use |
|---|---|
| `Complexity.pairEncode_getD` | the positional lookup law for doubled first fields |
| `Complexity.LogProg.inputLength_loop` | a bounded fragment counting the host length |
| `Complexity.LogProg.alignedPair_loop` | a stride-parametrized pair-shape check |

The first is used by target 8's lookup lemmas. The two loops are continuation infrastructure
for targets 8, 9 and 12, and do not by themselves claim those targets. All three print the
standard triple.

## Verification (maintainer)

- **Integrity.** All 27 `SHA256SUMS` entries are OK. The zip's C file
  (`evidence/lean-self-path.c`, an `LD_PRELOAD` shim for the agent's environment) is excluded:
  it was never compiled or run, and neither the patch nor any source references it. The
  agent's scripts (`final-sweep.sh`, `check-frozen.py`) were not run either.
- **Integration.** `git am -3` applied the one-patch series cleanly at the campaign tip
  `aed5b4ff` as `9ad832e7`, keeping the agent's authorship. The owned files are unchanged
  between the agent's base and the tip. Both changed files then match the delivered snapshots
  byte for byte. `PreimageHost`, `Reductions` and `Mult` are unchanged.
- **Freeze** (`audits/logs/b7-fill-2-freeze.log`, the maintainer's own check).
  - No statement changed. No public was removed. The only additions are the three flagged
    exports.
  - The only body change is target 7's.
  - 49 privates added: 43 in `InputAccess` and 6 in `QueryReshape`. No existing private
    changed.
  - Outside declarations, only flagged status text changed ("sorried" or "spec, fill pending"
    to "proved") and the three Main results bullets were added.
  - Imports are unchanged.
  - No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in
    the added lines.
- **Duplication** (`audits/logs/b7-fill-2-screen-after.txt`; base: the first delivery's after
  screen, `audits/logs/b7-fill-1-screen-after.txt`). 227 → 273 declarations, 58 → 67 pairs.
  - The 9 new pairs are all in-file, at 53–82%:
    - 7 in `InputAccess`, between the `access_*` step normalizations;
    - 2 in `QueryReshape`, the prefix/suffix address lemmas, both citing `pairEncode_getD`.
  - Each pair is justified in the report. None is at or above 90%, none is cross-file, and
    none of the first delivery's pairs disappeared. **New copies: none.** No ledger change.
- **Lint** (`audits/logs/b7-fill-2-stylelint.log`): 0 FAIL, 1 WARN over
  `TCSlib/Complexity/SpaceComplexity`, the size warning for `InputAccess`.
- **Sizes.**

  | File | Lines | Change |
  |---|---|---|
  | `InputAccess` | 1,569 | from 541 |
  | `QueryReshape` | 297 | from 195 |

  `InputAccess` crosses 1,000 lines. Justification: the continuation brief sets no size cap
  and forbids new files (ground rule 8), and file size alone is not a driver (user,
  2026-10-11).
- **Replay** (`audits/logs/b7-fill-2-replay.log`). 8 modules, the downstream closure of the
  two changed files, at `9ad832e7` into a snapshot of a tip-consistent olean tree; the user
  ran it from the maintainer's command. **0 errors.** 10 sorry warnings: `InputAccess` 0,
  `PreimageHost` 0, `QueryReshape` 2, `Reductions` 2, `Path` 2, `ImmermanSzelepcsenyi` 3,
  `Mult` 1. That is the first delivery's 11 minus target 7.
- **Axioms** (`audits/logs/b7-fill-2-axioms.log`; probe
  `audits/evidence/b7/B7Fill2Axioms.lean.txt`). The probe prints every public of `InputAccess`,
  `PreimageHost`, `QueryReshape`, `Reductions` and `Mult`, read-only against the replay's tree.
  - 40 of 45 are within `[propext, Classical.choice, Quot.sound]`.
  - Exactly targets 8–12 print `sorryAx`.
- **Admission walk** (`audits/logs/b7-fill-2-admissions.log`; probe
  `audits/evidence/b7/B7Fill2AdmissionWalk.lean.txt`). Each of targets 8–12 has itself as the
  only constant in its closure that mentions `sorryAx`. So no remaining target leans on
  another, and none leans on a helper.

## Disposition

- This partial goes in by PR, like the first delivery. The **B7 fill gate** runs once all
  twelve targets are complete, and covers every delivery.
- A second continuation brief, for targets 8–12, issues at the merged commit. It resumes at
  target 8 with the report's frontier: one mode-parametrized ARM over
  `![inputBitLang, inputLenLang]`, citing the three new exports and the six `QueryReshape`
  lemmas.
