# External audit pack — R8.0b fill gate (§12.8 stream D), round 2

Round 1 (`audits/s12-8-fill-D-findings.md`, attached verbatim) returned **FAIL: 0 blockers,
1 major, 2 minors, 11 notes**. Its notes confirm the fill itself. The dispositions are in
`audits/s12-8-fill-D-resolutions.md`, attached. The round-1 pack (`audits/s12-8-fill-D-pack.md`)
still describes the fill, whose Lean content is unchanged apart from the comment-only status
refresh below. The gate closes on zero blockers and zero majors. After it closes, the user
merges PR #38.

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| **F1** (major: no human acceptance of E1) | **The user accepted (2026-10-11) a one-off exception for exactly the `counterLoopTMVia`/`counterLoopTM` definition pair.** It is recorded in the resolutions, in the ledger's acknowledgment table (`audits/duplication-ledger.md`), and as `backlog.md` §1 **R80B-E1**. That is the named 12.2c follow-up you recommended: generic host first, `counterLoopTM` defined at `Function.Embedding.refl Bool`, consumers re-checked under its own gate. |
| **F2** (minor: missing inputs) | Attached: `Build/Catalog.lean` and `Build/Seam.lean` (the full six-file screen can now be re-run); the delivery's `SHA256SUMS`; the agent's full 74-module sweep; the axiom and admission-walk probe sources; and the false-control output. Archive integrity and non-execution of the shim and helpers remain maintainer attestations. |
| **F3** (minor: "nine" privates) | Erratum in the resolutions: eight alphabet generalizations, plus the authorized `counter_buffer_complement` proof replacement. |
| **F14** (note: refresh after the combined check) | The branch merged the campaign tip `fc999a8b`, where streams A–C have landed. The combined tree was replayed (8 modules, 0 errors, `CounterLoop` 0 sorry warnings); all 31 `CounterLoop` publics, R8.6 included, are admission-free. Then the status line got its comment-only refresh, at `d2c9e16c`. |

## Brief for the auditor

1. **F1.** Confirm that the recorded acceptance covers exactly the definition pair, no more,
   and that the 12.2c follow-up is specified as you recommended.
2. **F2.** Re-run the six-file screen from the attached sources if you wish. Report anything the
   newly attached evidence contradicts.
3. **The combined tree.** Check the round-2 replay and axiom logs
   (`audits/logs/s12-8-fill-D-r2-{replay,axioms}.log`). The merge of the tip is in the branch
   history. `CounterLoop.lean` at the head equals the round-1 audited file except for the
   status paragraph. A comment-stripped comparison is identical.
4. **The status refresh.** Check that the new status sentence is accurate.
5. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Combined-tree replay** (`audits/logs/s12-8-fill-D-r2-replay.log`, user-run, at
  `d2c9e16c`). Covers `CounterLoop`, `Inclusions`, `InputCall`, `CfgRecord`, `TQBF` and the
  three facades: **0 errors**. Sorry warnings: `Inclusions` 1 (B2b's open search contract),
  `CfgRecord` 1 (C's open step row), `TQBF` 4; **`CounterLoop` 0**.
* **Axioms** (`audits/logs/s12-8-fill-D-r2-axioms.log`; probe
  `audits/evidence/s12-8/S128FillDR2Axioms.lean.txt`). All 31 `CounterLoop` publics are within
  `[propext, Classical.choice, Quot.sound]`. The admission walk of `expandTM_run_ofCfg` and of
  both generic contracts is empty.
* **Instances** (`audits/logs/s12-8-fill-D-r2-instances.log`). `R80bInstances.lean.txt`
  re-run at the combined tree: 0 errors, 0 warnings. The false control (appendix
  `r80b-fill/control-appendix.lean.txt`) reports exactly its one appended error.
* **Status refresh.** Comment-only; comment-stripped code is identical (maintainer's check).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-8-fill-D-r2-findings.md`.
