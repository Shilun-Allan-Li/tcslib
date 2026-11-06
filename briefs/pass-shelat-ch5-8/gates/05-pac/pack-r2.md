# Gate 05 (Pass–shelat ch. 5–8, S3d layer 1), round 2: external closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194)
into `main`, at its head `6b781240bc438a103291c74b2ffefaa910f1a70d`.
- **Round 1** audited `44d27f39c233849a3a30a117bf15434610e485e9` and found **0 blockers, 1 major,
  8 minors and 7 notes** (`gate05-pac-findings.md`, in the bundle, verbatim).
- **The repair:** one commit, `6b781240`. Its full diff is `evidence-r2/repair.diff.txt`; each
  finding's resolution is in `resolutions-r1.md` (both in the bundle).
- **The deliverable:** **`gate05-pac-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] (PDF; book page = PDF page − 12; the item is on
book p. 179).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each of the 16 findings say whether the resolution
   is adequate: **fixed** (the defect is gone, and the fix introduces no new one), **recorded**
   (accepted as declared or scheduled, and the record is accurate), or **not resolved** (say why).
2. **It audits the changed surface afresh:** the rewritten deviations and docstrings, and the new
   theorem `not_pacLearnsUnder_const_pair` (restate it in your own words, and say whether its
   statement is what its docstring claims). Look for regressions: anything round 1 accepted that
   the repair broke. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 1 findings, resolutions, repair diff | `gate05-pac-findings.md`, `resolutions-r1.md`, `evidence-r2/repair.diff.txt` |
| Changed Lean, at `6b781240` | `TCSlib/InformationTheory/Samples.lean`, `TCSlib/LearningTheory/PAC/{Defs, Prediction}.lean`, `TCSlib/LearningTheory/PAC.lean` |
| Context | `policy.md`; `design/S3d-pac-learning.md` §"Layer 1" |

## Attestations (maintainer execution claims; `evidence-r2/`)

- **Elaboration:** the four changed modules, rechecked in import order at `6b781240`: all pass, with
  0 errors and 0 warnings (`checks.log`).
- **`sorry`:** none.
- **Axioms** (worker's run, reported): 37 of 38 theorems within `propext`, `Classical.choice` and
  `Quot.sound`; `PAC.label_apply` uses none.
- **Lint:** 0 findings in each of the four files.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 finding: `F<n>: fixed / recorded / not resolved — <reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major** (fixable
but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge case,
naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.
