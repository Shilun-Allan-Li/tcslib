# padded-cpa · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 4 minors, 3 notes).

Delivery: Claude worker, exchange `dffc2e7d` (`inbox/fills/padded-cpa/`), proof-branch tree
`be2bdbb2` (4 patches on `4a09f3993eb9344fc5714610e41ab141a0144db8`). Independent review on a
fresh worktree and a fresh olean tree; evidence `review-evidence.zip` (SHA-256
`f294ca6feebc0b9e2eee7d5581da58f3d5cd23008a0279632c3b57cb9bd2f0b9`; inner `SHA256SUMS`
`85eabe28931c472bc8a18cccebf825abd2c48c4d6f3eae1f2ce0848bd25d1b2c`, 351 entries, pins in
`PROVENANCE.txt`).

## Checks (all re-run by the reviewer)

- Integrity: `PAYLOAD-SHA256SUMS` 63/63; `git am` reproduces `src/` byte for byte and the
  worker's tree; diff 3 files, +889/−12.
- Build: the 233-module final order (the issued 221 plus 12 insertions, topologically sound,
  roots unchanged) 233/233 rc 0, 0 errors; the touched modules and `TrapdoorCPA` warning-free.
- Admissions 31 → 30 (only `padded_cpa`). Statements: 41 public ADDED, 0 CHANGED, 0 REMOVED;
  the target header byte-identical.
- Axioms: `padded_cpa` and `TrapdoorCollection.tdpBitScheme_padded_cpa` print
  `[propext, Classical.choice, Quot.sound]`; no new declaration uses another axiom.
- Rule 10: whole-file seals of all three files over their full TCSlib import closures
  (2,100 / 669 / 2,006 requests) rc 0 with 0 errors; base control clean; neither helper imports
  `OracleSecurity`. Controls 17/17 negatives fail once sealed, positives and unsealed pass.
  Explicit-reader scan: 388 items, 0 foreign definitions.
- Lint 0 FAIL (same 6 WARN as base, untouched files). Trial merges onto the campaign and #286
  textually clean.

## Findings and dispositions

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | `ChallengeSim.expect_sample_prod` repeats `Bridge.expect_sample_pair`'s proof; the report said "duplication: none". | **Landing edit:** proved from `Bridge.expect_sample_pair` (+ import `Games.Bridges.Experiments`). |
| 2 | minor | Generic `ProbComp` lemmas (`expect_sample_equiv/_comm/_unique`, `expect_sub`) published as `ChallengeSim.*`; unscoped `open ChallengeSim ProbComp`. | **Landing edit:** the `open` is scoped to `section PaddedCPA`. Promotion of the four lemmas to `Games/Probability.lean` is recorded as follow-up debt. |
| 3 | minor | `RecordHandler` uses `GGMRed.ofFn_padFin_of_length` via a transitive import; the fact has three copies. | Recorded as follow-up debt: promote `ofFn_padFin_of_length` beside `padFin` in `Asymptotic/Adversary.lean` and re-point. |
| 4 | minor | REPORT cites `evidence/seal/candidates.txt`, absent from the payload. | Recorded; the reviewer's independent seal supersedes it. |
| 5 | note | `OracleSecurity.lean` at 976 lines; the docstring did not name the helper modules. | **Landing edit:** helpers named under "Main results". Further growth triggers a split. |
| 6 | note | The new proofs cross `OracleSecurity`'s own `outLens` (in a private statement), `padded`, `indCodec` definitionally. | Allowed by the brief (own file); disclosed. |
| 7 | note | `chRun_toCompOn_transport` stated its formula only in words. | **Landing edit:** formula stated. |

## Landing

Landing branch `land/pass-shelat-padded-cpa` on the campaign head (Lean `ed0f7238`, after
#286): the worker's 4 commits plus one maintainer landing-edit commit. A fresh build of the
233-module closure on that head runs before the PR is opened.
