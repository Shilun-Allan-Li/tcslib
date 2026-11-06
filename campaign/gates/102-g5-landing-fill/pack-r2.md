# External audit pack, round 2: G5's landing, `Turing.FinTM.two_work_tapes_run` (PR #211, a fill gate)

**Round 1** (`pack.md`; findings `findings.md`; dispositions `resolutions.md`) was **HOLD, 0
blockers, 1 major, 1 minor, 5 notes**, with no soundness defect. Notes 3–7 verified the bundle,
the frozen statements, the boundary cases, the amortization, the seal and axiom evidence, the
landing repairs and the screen. The issues were:
- **Finding 1 (major):** `tt_forward_run`'s zero-time branch re-derived the imported
  `FinTM.not_computesInTime_zero`;
- **Finding 2 (minor):** `two_work_tapes_run`'s sketch said "each zone is kept half full", which
  misstates the invariant.

**The PR:** #211 on `lean/u2s-g5-landing`, head `e7e78aaf` (full hash in the bundle header):
round 1's head `f239dafd`, the repair `3a261ba2`, and a records-only merge of the campaign. One
file, `TwoTapes.lean`.

## What changed since round 1 (verify)

| Finding | Change (`3a261ba2`; `evidence/round2/round2-edits.diff`) |
|---|---|
| 1 | **Fixed** (the user's standing rule: a mechanical re-point in the PR). The branch is `exact not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)`, the auditor's proposed fix. A search of the library for the impossibility's other closing forms (`initCfg_eq` and `Cfg.init_state` rewrites ending in a contradiction) finds deterministic sites that already cite the lemma (`ClassP/DTIME`, `ClassNP/TMSAT`, `CookLevin/Hardness`, `Diagonalization/EXPCOM`) and two NDTM analogues with no published lemma (`ExhaustiveReplay`'s private `xr_not_haltsWithin_zero`, an inline step in `NDNormalForm`). The latter are outside #211 and recorded in the ledger as **NZ-1**, a promotion candidate awaiting the user |
| 2 | **Fixed.** The sketch: each side of a level is empty, half full or full, the two sides of a level hold a constant total, and a rebalance at index `i` restores every level below `i` to half full |

The freeze against round 1's head: only `tt_forward_run`'s body and `two_work_tapes_run`'s
docstring (`evidence/round2/freeze/`).

## Brief for the auditor

1. **Findings 1 and 2:** are both fixed, and is the NZ-1 search adequate?
2. **The repair itself:** does it change anything beyond the findings?

## Repository-side attestations (verify or challenge)

- **Replay** (`evidence/round2/merged-tree/`): `replay-lg7` at `e7e78aaf`, `TwoTapes`,
  `UniversalTlogT` and the `TuringMachine` facade, chained from the campaign's `oleans-lnth`:
  **3 modules, 0 failed, 0 `sorry`**; static 0 mismatches.
- **Rule 10** (`evidence/round2/seal/`): round 1's generator and 44-definition list re-run on the
  head's file: the sealed copy elaborates with **0 diagnostics** on `oleans-lg7`; controls **91
  pass unsealed, 91 fail sealed**.
- **Axioms** (`evidence/round2/seal/`): `two_work_tapes_run`, `two_work_tapes_binary` and
  `Turing.universal_TlogT` on `[propext, Classical.choice, Quot.sound]`; all 104 declarations
  within those three, no `sorryAx`.
- **Screen** (`evidence/round2/screen/`): the 22-file population at the head: **1,277 declarations, 840 pairs,
  288,323 characters**, identical to round 1's (0 new, 0 gone).
- **Lint** (`evidence/round2/lint/`): unchanged from round 1 (0 FAIL, 72 WARN over 92 files; the
  policy linter's one finding, the size).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/102-g5-landing-fill/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `g5-landing-fill-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
