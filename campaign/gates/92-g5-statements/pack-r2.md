# External audit pack, round 2: G5's statements (PR #189, a statement gate)

**Round 1** (`pack.md`; findings `findings.md`; resolutions `resolutions.md`) was **DO NOT CLOSE,
0 blockers, 1 major, 3 minors**. The statements were found sound, and the Hennie–Stearns
admission is authorized. **Ruled (user, 2026-11-04): fix all now.**

**The PR now:** #189 at `9e96f6463e840ee775d8e6025bd245b45d68f5bd`:
- `caa6bf53`, the fixes (`evidence/round2/patches/`);
- then a merge of campaign records, which changes no Lean.

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| 1, `two_work_tapes_binary` | `(computesFunInTime_iff _ _ _).2 fun x => h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)`; no reduction of `FinTM.ComputesFunInTime` |
| 2, `FinTM.stateEquivFin` | `FinTM.stateEquivFin_eq`, its defining equation (`rfl`, no `simp` attribute) |
| 3, `alphabet_reduction_run`'s docstring | "Without an image hypothesis the converse cannot in general assert `o = w.map e`: …" |
| 4, the replay | `replay-lg5` passed (325/325, its log in `evidence/merged-tree/`); round 2's is `replay-lg5b` |

## Brief for the auditor

1. Are the fixes correct, statement-preserving and rule-10 compliant?
2. **The seal now covers `two_work_tapes_binary`** (`evidence/round2/rule10/`): five sealed copies
   (`ARSealed`, `ENSealed`, `C2Sealed`, `TTSealed`, `UTSealed`) under a seal of 15 definitions,
   `FinTM.ComputesFunInTime` added. Each copy elaborates with 0 errors; the only output is the
   pre-existing `sorry` warnings. Controls: 30 of 30 pass unsealed, and 0 of 30 pass sealed. Is
   any proof site of the PR still uncovered?
3. Do the record corrections answer findings 2–4?

## Repository-side attestations (verify or challenge)

- **Compilation:** the five changed modules recompiled into the round-1 clone with only the
  expected warnings (`two_work_tapes_run`'s `sorry`, and `Encoding`'s pre-existing one).
- **Axioms** (`evidence/round2/axioms/`): as in round 1, plus `stateEquivFin_eq` on the standard
  three.
- **Lint:** campaign lint 0 FAIL / 71 WARN. Check 8 no longer lists `stateEquivFin`.
- **Replay:** `replay-lg5b` (`evidence/round2/merged-tree/`), 325 modules from `oleans-ledge`, at
  the head.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/92-g5-statements/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `g5-statements-r2-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
