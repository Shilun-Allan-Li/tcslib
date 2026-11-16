# seq-zk · maintainer delivery review (r1)

**Verdict: ACCEPT** (all five targets proved). S-01 is confirmed and S-02 is pending as LE-doc. Draft [PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327).

## Delivery and landing
- **Delivery:** Codex on Seyoon's Mac, a lead and 3 sub-agents. The final is exchange `a6be22fa`; the checkpoints are `d316d29a`, `36f1896d` and `65bc1c08`. The issue base is `107f1e8c`.
- **Landing:** `land/pass-shelat-seq-zk`, on `05d26fe5`.
  - **Head:** `e9b5ea47a1c3dcd664caf2dbf308f89c1beffbb8`, tree `a6acdfbf`.
  - **Commits:** `1ed5765c`, `29b81e8b`, `9747e27a`, `a1a5c447`, `5fa0430c` and `e9b5ea47`.
- **Files:** 41 files, +6491/−14:
  - `Composability/SequentialZK.lean`;
  - 39 new helpers under `SequentialZK/`;
  - `ZeroKnowledge/Defs.lean`, +9 lines (`StatZK_iff`).
- **Evidence:** `review-evidence.zip`, SHA-256 `f9c394794fd7637237a274163a396eaa78452250c5e31abc5d2878b9e353392f`, with 1107 entries.

## Checks
- **Sub-agents:**
  - `evidence/subagents/seq-zk-{a,b,c}` exist.
  - `REPORT.md` assigns each of the 39 helpers to exactly one agent: the lead 5, a 10, b 9 and c 15.
  - `SequentialZK.lean` and `Defs` are the lead's.
  - The lead ran the final sweep: all 276 checks match lead-tagged slot acquisitions.
  - Never more than 3 slots were held at once.
- **Integrity:** the manifests verify 3073/3073 and 3023/3023. `git am` reproduces the 6 hashes unsigned. The package verifies 7/7 and its sources 237/237.
- **Build:** 303 modules give rc 0 and 0 errors, through root `TCSlib` and both `Checks`, in 1670 s. The whole-tree check covers 1288 modules: OK.
- **Statements:** the header, prose and definition-body checks show 0 differences, and the control reports 1. decls2 gives 196 ADDED and 0 CHANGED. The largest file has 990 lines and the widest line is 99 characters. There is no `@[simp]`.
- **Axioms:** the five targets, `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and the `ThreeColoring` consumers use only the standard three. 414 constants; no `sorryAx`.
- **Rule 10:** 154 runs. Only `Defs` fails: 10 errors in the same 6 declarations that already fail at the base. `StatZK_iff` is clean. The coe controls are ALL_OK. The scan finds 0 foreign definitions.
- **Admissions:** 23 → 18.
- **Lint:** 92/101 and 25/391.
- **Content:** each target is a thin instantiation of the helper theorems. The sketches describe the delivered route.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| S-01 | minor | The frozen `ZeroKnowledge/Defs.lean` gains `StatZK_iff` (`Iff.rfl`). It equals the approved patch, apart from the position of one blank line. The approval had been recorded only in the delivery. | **Confirmed by Seyoon (2026-11-16).** Accepted. |
| S-02 | minor | 88 new public declarations' docstrings give no formula. | LE-doc, pending, before the gate. |
| S-03 | info | A disclosed unused `hQ` warning; the Prop-valued instance `PhaseMetadata.instNonempty`; and some tool artifacts. | None. |
